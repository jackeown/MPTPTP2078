%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   87 (3082 expanded)
%              Number of clauses        :   70 ( 924 expanded)
%              Number of leaves         :    8 ( 744 expanded)
%              Depth                    :   15
%              Number of atoms          :  519 (54699 expanded)
%              Number of equality atoms :   13 (4131 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :  111 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_tmap_1,conjecture,(
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
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( ( u1_struct_0(X1) = u1_struct_0(X2)
                  & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                       => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X2))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X2,X3,X5,X7) )
                                   => r1_tmap_1(X1,X3,X4,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tmap_1)).

fof(t48_tmap_1,axiom,(
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
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_tmap_1(X1,X2,X3,X4)
                  <=> ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                       => ~ ( v3_pre_topc(X5,X2)
                            & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
                            & ! [X6] :
                                ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
                               => ~ ( v3_pre_topc(X6,X1)
                                    & r2_hidden(X4,X6)
                                    & r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X6),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_8,negated_conjecture,(
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
                  & v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( ( u1_struct_0(X1) = u1_struct_0(X2)
                    & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                         => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X1))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tmap_1(X2,X3,X5,X7) )
                                     => r1_tmap_1(X1,X3,X4,X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_tmap_1])).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24,X27] :
      ( ( m1_subset_1(esk1_5(X20,X21,X22,X23,X24),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ v3_pre_topc(X24,X21)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v3_pre_topc(esk1_5(X20,X21,X22,X23,X24),X20)
        | ~ v3_pre_topc(X24,X21)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(X23,esk1_5(X20,X21,X22,X23,X24))
        | ~ v3_pre_topc(X24,X21)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r1_tarski(k7_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,esk1_5(X20,X21,X22,X23,X24)),X24)
        | ~ v3_pre_topc(X24,X21)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X20),u1_struct_0(X21),X22,X23),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_4(X20,X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v3_pre_topc(esk2_4(X20,X21,X22,X23),X21)
        | r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(k3_funct_2(u1_struct_0(X20),u1_struct_0(X21),X22,X23),esk2_4(X20,X21,X22,X23))
        | r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ v3_pre_topc(X27,X20)
        | ~ r2_hidden(X23,X27)
        | ~ r1_tarski(k7_relset_1(u1_struct_0(X20),u1_struct_0(X21),X22,X27),esk2_4(X20,X21,X22,X23))
        | r1_tmap_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tmap_1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & u1_struct_0(esk3_0) = u1_struct_0(esk4_0)
    & r1_tarski(u1_pre_topc(esk4_0),u1_pre_topc(esk3_0))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk4_0))
    & esk8_0 = esk9_0
    & r1_tmap_1(esk4_0,esk5_0,esk7_0,esk9_0)
    & ~ r1_tmap_1(esk3_0,esk5_0,esk6_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),esk2_4(X1,X2,X3,X4))
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r1_funct_2(X10,X11,X12,X13,X14,X15)
        | X14 = X15
        | v1_xboole_0(X11)
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X10,X11)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( X14 != X15
        | r1_funct_2(X10,X11,X12,X13,X14,X15)
        | v1_xboole_0(X11)
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X10,X11)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X31,X32,X33] :
      ( ~ r2_hidden(X31,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X33))
      | ~ v1_xboole_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk5_0,esk6_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk5_0),esk6_0,X1),esk2_4(esk3_0,esk5_0,esk6_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( v3_pre_topc(esk2_4(X1,X2,X3,X4),X2)
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk5_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk5_0),esk6_0,esk8_0),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_4(esk3_0,esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk5_0,esk6_0,X1)
    | v3_pre_topc(esk2_4(esk3_0,esk5_0,esk6_0,X1),esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk5_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 = esk6_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_12]),c_0_37]),c_0_15]),c_0_38]),c_0_16])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29])).

cnf(c_0_47,plain,
    ( v3_pre_topc(esk1_5(X1,X2,X3,X4,X5),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_52,plain,(
    ! [X8,X9] :
      ( ( ~ v3_pre_topc(X9,X8)
        | r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(X9,u1_pre_topc(X8))
        | v3_pre_topc(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_53,negated_conjecture,
    ( v2_struct_0(X1)
    | v3_pre_topc(esk1_5(X1,esk5_0,X2,X3,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),X1)
    | ~ r1_tmap_1(X1,esk5_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk5_0),X2,X3),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_13]),c_0_46]),c_0_17])]),c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_5(X1,esk5_0,X2,X3,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tmap_1(X1,esk5_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk5_0),X2,X3),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_13]),c_0_46]),c_0_17])]),c_0_19])).

fof(c_0_59,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | m1_subset_1(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_23]),c_0_12]),c_0_15]),c_0_23]),c_0_40]),c_0_23]),c_0_16]),c_0_23]),c_0_28]),c_0_56])]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_54]),c_0_23]),c_0_55]),c_0_23]),c_0_12]),c_0_15]),c_0_23]),c_0_40]),c_0_23]),c_0_16]),c_0_23]),c_0_28]),c_0_56])]),c_0_57])).

fof(c_0_63,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_23]),c_0_62]),c_0_56])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_68,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X16,X17)
      | v1_xboole_0(X17)
      | r2_hidden(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),X1)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(u1_pre_topc(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X1,X2,X3,X4,X5)),X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,esk1_5(X2,X3,X4,X1,X5))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X5,X3)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X1),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tmap_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_77,plain,
    ( r1_tmap_1(X2,X4,X5,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X4),X5,X1),esk2_4(X2,X4,X5,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(esk5_0),X2,esk1_5(X1,esk5_0,X2,X3,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ r1_tmap_1(X1,esk5_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk5_0),X2,X3),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_48]),c_0_13]),c_0_46]),c_0_17])]),c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(X2,esk1_5(X1,esk5_0,X3,X2,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)))
    | ~ r1_tmap_1(X1,esk5_0,X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk5_0),X3,X2),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_48]),c_0_13]),c_0_46]),c_0_17])]),c_0_19])).

cnf(c_0_80,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_82,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X5),esk2_4(X1,X2,X3,X4))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,X5)
    | ~ v3_pre_topc(X5,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_77,c_0_64])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk5_0),esk6_0,esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_54]),c_0_23]),c_0_55]),c_0_23]),c_0_12]),c_0_15]),c_0_23]),c_0_40]),c_0_23]),c_0_16]),c_0_23]),c_0_28]),c_0_56])]),c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_54]),c_0_55]),c_0_23]),c_0_12]),c_0_15]),c_0_23]),c_0_40]),c_0_23]),c_0_16]),c_0_23]),c_0_28]),c_0_56])]),c_0_57])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(esk1_5(esk4_0,esk5_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_62]),c_0_18])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_13]),c_0_14]),c_0_12]),c_0_15]),c_0_84]),c_0_85]),c_0_16]),c_0_62]),c_0_17]),c_0_18])]),c_0_29]),c_0_19]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
