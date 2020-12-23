%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1725+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:39 EST 2020

% Result     : Theorem 20.37s
% Output     : CNFRefutation 20.37s
% Verified   : 
% Statistics : Number of formulae       :  108 (6616 expanded)
%              Number of clauses        :   93 (2036 expanded)
%              Number of leaves         :    7 (1587 expanded)
%              Depth                    :   38
%              Number of atoms          :  729 (88260 expanded)
%              Number of equality atoms :   12 ( 468 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_tmap_1,conjecture,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ( ( m1_pre_topc(X2,X4)
                       => ( ~ r1_tsep_1(k2_tsep_1(X1,X4,X3),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X1,X3,X4),X2) ) )
                      & ( m1_pre_topc(X3,X4)
                       => ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X4),X3)
                          & ~ r1_tsep_1(k2_tsep_1(X1,X4,X2),X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).

fof(t32_tmap_1,axiom,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ( ( m1_pre_topc(X2,X4)
                       => m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X3)) )
                      & ( m1_pre_topc(X3,X4)
                       => m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(t29_tsep_1,axiom,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ( ~ r1_tsep_1(X2,X3)
                     => k2_tsep_1(X1,X2,X3) = k2_tsep_1(X1,X3,X2) )
                    & ( ( ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4) )
                        | ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X2,k2_tsep_1(X1,X3,X4)) ) )
                     => k2_tsep_1(X1,k2_tsep_1(X1,X2,X3),X4) = k2_tsep_1(X1,X2,k2_tsep_1(X1,X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tsep_1)).

fof(t23_tmap_1,axiom,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(t22_tmap_1,axiom,(
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
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(c_0_7,negated_conjecture,(
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
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( ~ r1_tsep_1(X2,X3)
                     => ( ( m1_pre_topc(X2,X4)
                         => ( ~ r1_tsep_1(k2_tsep_1(X1,X4,X3),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X1,X3,X4),X2) ) )
                        & ( m1_pre_topc(X3,X4)
                         => ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X4),X3)
                            & ~ r1_tsep_1(k2_tsep_1(X1,X4,X2),X3) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_tmap_1])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ m1_pre_topc(X23,X25)
        | m1_pre_topc(k2_tsep_1(X22,X23,X24),k2_tsep_1(X22,X25,X24))
        | r1_tsep_1(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_pre_topc(X24,X25)
        | m1_pre_topc(k2_tsep_1(X22,X23,X24),k2_tsep_1(X22,X23,X25))
        | r1_tsep_1(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_tmap_1])])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ r1_tsep_1(esk2_0,esk3_0)
    & ( m1_pre_topc(esk3_0,esk4_0)
      | m1_pre_topc(esk2_0,esk4_0) )
    & ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
      | m1_pre_topc(esk2_0,esk4_0) )
    & ( m1_pre_topc(esk3_0,esk4_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) )
    & ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_10,plain,
    ( m1_pre_topc(k2_tsep_1(X3,X4,X1),k2_tsep_1(X3,X4,X2))
    | r1_tsep_1(X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r1_tsep_1(X16,X17)
        | k2_tsep_1(X15,X16,X17) = k2_tsep_1(X15,X17,X16)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_tsep_1(X16,X17)
        | r1_tsep_1(k2_tsep_1(X15,X16,X17),X18)
        | k2_tsep_1(X15,k2_tsep_1(X15,X16,X17),X18) = k2_tsep_1(X15,X16,k2_tsep_1(X15,X17,X18))
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_tsep_1(X17,X18)
        | r1_tsep_1(X16,k2_tsep_1(X15,X17,X18))
        | k2_tsep_1(X15,k2_tsep_1(X15,X16,X17),X18) = k2_tsep_1(X15,X16,k2_tsep_1(X15,X17,X18))
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_tsep_1])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,X1),k2_tsep_1(esk1_0,esk2_0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_tsep_1(X1,X2)
    | k2_tsep_1(X3,X1,X2) = k2_tsep_1(X3,X2,X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,X1),k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,X2) = k2_tsep_1(esk1_0,X2,X1)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_12]),c_0_13])]),c_0_19]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk4_0) = k2_tsep_1(esk1_0,esk4_0,X1)
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19])).

fof(c_0_29,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_tsep_1(X13,X14)
        | r1_tsep_1(X12,X14)
        | ~ m1_pre_topc(X12,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r1_tsep_1(X14,X13)
        | r1_tsep_1(X12,X14)
        | ~ m1_pre_topc(X12,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r1_tsep_1(X13,X14)
        | r1_tsep_1(X14,X12)
        | ~ m1_pre_topc(X12,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r1_tsep_1(X14,X13)
        | r1_tsep_1(X14,X12)
        | ~ m1_pre_topc(X12,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_11]),c_0_14])).

fof(c_0_32,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v2_struct_0(k2_tsep_1(X5,X6,X7))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5) )
      & ( v1_pre_topc(k2_tsep_1(X5,X6,X7))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5) )
      & ( m1_pre_topc(k2_tsep_1(X5,X6,X7),X5)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_33,plain,
    ( r1_tsep_1(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19]),c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk3_0) = k2_tsep_1(esk1_0,esk3_0,X1)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_24])).

cnf(c_0_39,plain,
    ( r1_tsep_1(X3,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_18]),c_0_11]),c_0_13])]),c_0_19]),c_0_14]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_23]),c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk2_0) = k2_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_11]),c_0_23]),c_0_14])).

cnf(c_0_44,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,plain,(
    ! [X19,X20,X21] :
      ( ( m1_pre_topc(k2_tsep_1(X19,X20,X21),X20)
        | r1_tsep_1(X20,X21)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_pre_topc(k2_tsep_1(X19,X20,X21),X21)
        | r1_tsep_1(X20,X21)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_12]),c_0_11]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_43]),c_0_11]),c_0_22]),c_0_13])]),c_0_14]),c_0_24]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_11]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_22]),c_0_13])]),c_0_24]),c_0_15])).

cnf(c_0_51,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r1_tsep_1(X9,X10)
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r1_tsep_1(X10,X9)
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_18]),c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_11]),c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_22]),c_0_12]),c_0_13])]),c_0_24]),c_0_15])).

cnf(c_0_57,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_12]),c_0_55]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_11]),c_0_23]),c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),c_0_24]),c_0_48])).

cnf(c_0_61,plain,
    ( m1_pre_topc(k2_tsep_1(X3,X1,X4),k2_tsep_1(X3,X2,X4))
    | r1_tsep_1(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_12]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),k2_tsep_1(esk1_0,X2,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_12]),c_0_13])]),c_0_24]),c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_62]),c_0_19]),c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_66,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_18]),c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_23]),c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_66]),c_0_18]),c_0_22]),c_0_13])]),c_0_19]),c_0_24]),c_0_15])).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_11]),c_0_23]),c_0_14])).

cnf(c_0_72,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_18]),c_0_12]),c_0_11]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(X1,esk2_0)
    | m1_pre_topc(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_69]),c_0_14]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_75,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_76,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | m1_pre_topc(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_48])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_22]),c_0_12]),c_0_13])]),c_0_24]),c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_12]),c_0_55]),c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_11]),c_0_23]),c_0_14])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | m1_pre_topc(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_79]),c_0_80])]),c_0_14]),c_0_48])).

cnf(c_0_83,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_66])).

cnf(c_0_84,plain,
    ( r1_tsep_1(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_85,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_55]),c_0_12]),c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_86,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_31])).

cnf(c_0_87,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_19]),c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_86]),c_0_14]),c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_72]),c_0_23]),c_0_14])).

cnf(c_0_90,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_74]),c_0_48])).

cnf(c_0_91,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_18]),c_0_12]),c_0_22]),c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_92,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_77]),c_0_12]),c_0_55]),c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_93,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_92]),c_0_80])]),c_0_14]),c_0_48])).

cnf(c_0_95,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_31])).

cnf(c_0_96,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_55]),c_0_12]),c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_97,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_95]),c_0_72])]),c_0_19]),c_0_14])).

cnf(c_0_98,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_96]),c_0_24]),c_0_41])).

cnf(c_0_99,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_18]),c_0_12]),c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_100,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_54]),c_0_12]),c_0_55]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_102,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_101]),c_0_59])]),c_0_24]),c_0_48])).

cnf(c_0_103,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_55]),c_0_12]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_104,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_103]),c_0_91])]),c_0_19]),c_0_24])).

cnf(c_0_105,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_18]),c_0_12]),c_0_22]),c_0_13])]),c_0_15])).

cnf(c_0_106,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_105]),c_0_72])]),c_0_19]),c_0_14])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_18]),c_0_12]),c_0_11]),c_0_13])]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
