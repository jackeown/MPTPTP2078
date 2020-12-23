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
% DateTime   : Thu Dec  3 11:17:10 EST 2020

% Result     : Theorem 50.22s
% Output     : CNFRefutation 50.22s
% Verified   : 
% Statistics : Number of formulae       :  399 (103217 expanded)
%              Number of clauses        :  370 (33495 expanded)
%              Number of leaves         :   14 (25203 expanded)
%              Depth                    :   26
%              Number of atoms          : 1820 (1225869 expanded)
%              Number of equality atoms :   88 (6778 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tsep_1)).

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

fof(t31_tsep_1,axiom,(
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
               => ( ( m1_pre_topc(X2,X3)
                   => k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X3) )
                  & ( m1_pre_topc(X3,X2)
                   => k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) )
                  & ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                   => m1_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_tsep_1(X24,X25)
        | r1_tsep_1(X23,X25)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tsep_1(X25,X24)
        | r1_tsep_1(X23,X25)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tsep_1(X24,X25)
        | r1_tsep_1(X25,X23)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tsep_1(X25,X24)
        | r1_tsep_1(X25,X23)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

fof(c_0_18,plain,(
    ! [X37] :
      ( ~ l1_pre_topc(X37)
      | m1_pre_topc(X37,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_21]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

fof(c_0_33,plain,(
    ! [X38,X39,X40] :
      ( ( m1_pre_topc(k2_tsep_1(X38,X39,X40),X39)
        | r1_tsep_1(X39,X40)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_pre_topc(k2_tsep_1(X38,X39,X40),X40)
        | r1_tsep_1(X39,X40)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

fof(c_0_34,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_struct_0(k1_tsep_1(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10) )
      & ( v1_pre_topc(k1_tsep_1(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10) )
      & ( m1_pre_topc(k1_tsep_1(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_35,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X26)
      | k1_tsep_1(X26,X27,X27) = g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_37,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_39,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_tsep_1(X17,X18)
        | ~ m1_pre_topc(X17,X18)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r1_tsep_1(X18,X17)
        | ~ m1_pre_topc(X17,X18)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20])]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk1_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_32])]),c_0_24])).

cnf(c_0_42,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X33,X34,X35,X36] :
      ( ( r1_tsep_1(X34,X35)
        | k2_tsep_1(X33,X34,X35) = k2_tsep_1(X33,X35,X34)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r1_tsep_1(X34,X35)
        | r1_tsep_1(k2_tsep_1(X33,X34,X35),X36)
        | k2_tsep_1(X33,k2_tsep_1(X33,X34,X35),X36) = k2_tsep_1(X33,X34,k2_tsep_1(X33,X35,X36))
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r1_tsep_1(X35,X36)
        | r1_tsep_1(X34,k2_tsep_1(X33,X35,X36))
        | k2_tsep_1(X33,k2_tsep_1(X33,X34,X35),X36) = k2_tsep_1(X33,X34,k2_tsep_1(X33,X35,X36))
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_tsep_1])])])])])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_36]),c_0_21])])).

cnf(c_0_47,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_38]),c_0_21])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk4_0)
    | ~ r1_tsep_1(esk1_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20])]),c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_23]),c_0_21])]),c_0_24])).

fof(c_0_54,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | v2_struct_0(X20)
      | ~ m1_pre_topc(X20,X19)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,X19)
      | m1_pre_topc(X20,k1_tsep_1(X19,X20,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,X2),esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk4_0,esk4_0) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_21]),c_0_23])]),c_0_25]),c_0_24])).

fof(c_0_57,plain,(
    ! [X41,X42,X43] :
      ( ( ~ m1_pre_topc(X42,X43)
        | k2_tsep_1(X41,X42,X43) = g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X41)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( k2_tsep_1(X41,X42,X43) != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | m1_pre_topc(X42,X43)
        | r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X41)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ m1_pre_topc(X43,X42)
        | k2_tsep_1(X41,X42,X43) = g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43))
        | r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X41)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( k2_tsep_1(X41,X42,X43) != g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43))
        | m1_pre_topc(X43,X42)
        | r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X41)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_tsep_1])])])])])).

cnf(c_0_58,plain,
    ( r1_tsep_1(X2,X3)
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_21]),c_0_23])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_38]),c_0_21]),c_0_23])]),c_0_24]),c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_21]),c_0_23])]),c_0_24]),c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r1_tsep_1(esk1_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_30])]),c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk4_0),esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_20]),c_0_25])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_20]),c_0_21]),c_0_23])])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_20])]),c_0_25])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_72,plain,
    ( k2_tsep_1(X3,X2,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | r1_tsep_1(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_38]),c_0_21]),c_0_23])]),c_0_24]),c_0_48])).

cnf(c_0_74,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_75,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,X2) = k2_tsep_1(esk1_0,X2,X1)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_20]),c_0_21]),c_0_23])]),c_0_25]),c_0_24])).

cnf(c_0_76,negated_conjecture,
    ( k2_tsep_1(esk3_0,X1,X2) = k2_tsep_1(esk3_0,X2,X1)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_46]),c_0_61])]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_38])]),c_0_48])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_20])]),c_0_25])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk1_0,esk4_0),esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_32])]),c_0_24])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk4_0,X1,esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_30]),c_0_27]),c_0_69])]),c_0_25])).

cnf(c_0_82,negated_conjecture,
    ( k1_tsep_1(esk4_0,esk4_0,esk4_0) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_27]),c_0_69])]),c_0_25])).

cnf(c_0_83,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_70]),c_0_21])])).

cnf(c_0_84,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_70]),c_0_21]),c_0_23])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_56]),c_0_20]),c_0_21])]),c_0_25]),c_0_24])).

cnf(c_0_86,plain,
    ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_72,c_0_51])).

cnf(c_0_87,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_63]),c_0_38])]),c_0_48])).

cnf(c_0_88,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_38]),c_0_48])).

cnf(c_0_89,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk2_0,esk2_0) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_21]),c_0_23])]),c_0_48]),c_0_24])).

fof(c_0_90,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v2_struct_0(k2_tsep_1(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13) )
      & ( v1_pre_topc(k2_tsep_1(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13) )
      & ( m1_pre_topc(k2_tsep_1(X13,X14,X15),X13)
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk3_0) = k2_tsep_1(esk1_0,esk3_0,X1)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_36]),c_0_50])).

cnf(c_0_93,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk2_0) = k2_tsep_1(esk1_0,esk2_0,X1)
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_38]),c_0_48])).

cnf(c_0_94,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_36]),c_0_21]),c_0_23])]),c_0_24]),c_0_50])).

cnf(c_0_95,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk3_0,X1,X2),X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_61]),c_0_46])]),c_0_50])).

cnf(c_0_96,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_97,negated_conjecture,
    ( k2_tsep_1(esk3_0,X1,esk3_0) = k2_tsep_1(esk3_0,esk3_0,X1)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_60]),c_0_50])).

cnf(c_0_98,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk4_0),esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_67])).

cnf(c_0_99,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_36]),c_0_38])]),c_0_79]),c_0_50]),c_0_48])).

cnf(c_0_100,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk1_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_82]),c_0_83]),c_0_82]),c_0_84]),c_0_30])]),c_0_85]),c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_102,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk2_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_38])]),c_0_48])).

cnf(c_0_103,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_21]),c_0_23])])).

cnf(c_0_104,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_89]),c_0_38])]),c_0_48])).

cnf(c_0_105,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_106,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_36]),c_0_50])).

cnf(c_0_107,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_108,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk2_0) = k2_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_92]),c_0_38])]),c_0_48])).

cnf(c_0_109,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk2_0) = k2_tsep_1(esk1_0,esk2_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_93]),c_0_48])).

cnf(c_0_110,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_21]),c_0_23])]),c_0_24]),c_0_48])).

cnf(c_0_111,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_60]),c_0_36])]),c_0_50])).

cnf(c_0_112,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk3_0,X1,esk3_0),esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_60]),c_0_50])).

cnf(c_0_113,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk3_0) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_21]),c_0_23])]),c_0_50]),c_0_24])).

cnf(c_0_114,negated_conjecture,
    ( k2_tsep_1(esk3_0,X1,esk3_0) = k2_tsep_1(esk3_0,esk3_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_50])).

cnf(c_0_115,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_98]),c_0_20]),c_0_38])]),c_0_25]),c_0_48])).

cnf(c_0_116,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_98]),c_0_38])]),c_0_48])).

cnf(c_0_117,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_118,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_36]),c_0_21]),c_0_23])]),c_0_24]),c_0_50])).

cnf(c_0_119,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_70]),c_0_21]),c_0_23])]),c_0_24]),c_0_85])).

cnf(c_0_120,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_32]),c_0_20])]),c_0_25]),c_0_24])).

cnf(c_0_121,negated_conjecture,
    ( r1_tsep_1(X1,esk1_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_24])).

cnf(c_0_122,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_102]),c_0_63])]),c_0_48])).

cnf(c_0_123,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk2_0,X1,esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_63]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_124,negated_conjecture,
    ( k1_tsep_1(esk2_0,esk2_0,esk2_0) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_63]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_125,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_104]),c_0_21])])).

cnf(c_0_126,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_104]),c_0_21]),c_0_23])])).

cnf(c_0_127,negated_conjecture,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_89]),c_0_38]),c_0_21])]),c_0_48]),c_0_24])).

cnf(c_0_128,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_21]),c_0_24])).

cnf(c_0_129,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_106]),c_0_38])]),c_0_48])).

cnf(c_0_130,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_38]),c_0_36]),c_0_21])]),c_0_48]),c_0_50]),c_0_24])).

cnf(c_0_131,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk2_0) = k2_tsep_1(esk1_0,esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_38]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_132,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk1_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_38]),c_0_32])]),c_0_24])).

cnf(c_0_133,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_50])).

cnf(c_0_134,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_36]),c_0_60])]),c_0_50])).

cnf(c_0_135,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_113]),c_0_36])]),c_0_50])).

cnf(c_0_136,negated_conjecture,
    ( k2_tsep_1(esk3_0,X1,esk3_0) = k2_tsep_1(esk3_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_60]),c_0_46]),c_0_61])]),c_0_50])).

cnf(c_0_137,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_115]),c_0_25]),c_0_48]),c_0_116])).

cnf(c_0_138,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_20]),c_0_21]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_139,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_60]),c_0_36])]),c_0_50])).

cnf(c_0_140,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_20])]),c_0_25])).

cnf(c_0_141,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_65]),c_0_25]),c_0_50]),c_0_27]),c_0_69])])).

cnf(c_0_142,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0),esk1_0)
    | ~ m1_pre_topc(esk1_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_121]),c_0_24])).

cnf(c_0_143,plain,
    ( k2_tsep_1(X3,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_144,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124]),c_0_124]),c_0_125]),c_0_124]),c_0_126]),c_0_63])]),c_0_127]),c_0_48])).

cnf(c_0_145,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | l1_pre_topc(k2_tsep_1(esk1_0,X2,X1))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_128]),c_0_21])])).

cnf(c_0_146,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_129]),c_0_49]),c_0_103])]),c_0_48]),c_0_130])).

cnf(c_0_147,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk3_0) = k2_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_92]),c_0_50])).

cnf(c_0_148,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X4)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X2,X3),X4)
    | ~ m1_pre_topc(X4,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_128]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_149,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk2_0) = k2_tsep_1(esk1_0,esk2_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_93]),c_0_48])).

cnf(c_0_150,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,X1,esk2_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_131]),c_0_38]),c_0_21])]),c_0_48]),c_0_24])).

cnf(c_0_151,negated_conjecture,
    ( ~ r1_tsep_1(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_132]),c_0_36])]),c_0_50])).

cnf(c_0_152,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_133]),c_0_38])]),c_0_48])).

cnf(c_0_153,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk3_0,X1,X2),esk3_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_46]),c_0_50])).

cnf(c_0_154,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_134]),c_0_60])]),c_0_50])).

cnf(c_0_155,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk3_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_60]),c_0_46]),c_0_61])]),c_0_50])).

cnf(c_0_156,negated_conjecture,
    ( k1_tsep_1(esk3_0,esk3_0,esk3_0) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_60]),c_0_46]),c_0_61])]),c_0_50])).

cnf(c_0_157,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_135]),c_0_21])])).

cnf(c_0_158,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_135]),c_0_21]),c_0_23])])).

cnf(c_0_159,negated_conjecture,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_113]),c_0_36]),c_0_21])]),c_0_50]),c_0_24])).

cnf(c_0_160,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(esk3_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_136]),c_0_60]),c_0_46])]),c_0_50])).

cnf(c_0_161,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X3,X4)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X4)
    | ~ m1_pre_topc(X4,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_128]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_162,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_38]),c_0_20]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_163,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_81]),c_0_82]),c_0_82]),c_0_82]),c_0_70]),c_0_30])]),c_0_85]),c_0_25])).

cnf(c_0_164,negated_conjecture,
    ( r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ r1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_70]),c_0_36])]),c_0_85]),c_0_50])).

cnf(c_0_165,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_65]),c_0_30])]),c_0_25])).

cnf(c_0_166,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X2,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_129]),c_0_49]),c_0_103])]),c_0_48]),c_0_130])).

cnf(c_0_167,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_32]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_168,plain,
    ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_143,c_0_96])).

cnf(c_0_169,negated_conjecture,
    ( l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_144]),c_0_49])])).

cnf(c_0_170,plain,
    ( r1_tsep_1(X1,X2)
    | r1_tsep_1(k2_tsep_1(X3,X1,X2),X4)
    | k2_tsep_1(X3,k2_tsep_1(X3,X1,X2),X4) = k2_tsep_1(X3,X1,k2_tsep_1(X3,X2,X4))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_171,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X4,X3)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X4)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X4,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_128]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_172,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),k2_tsep_1(esk1_0,X1,X2))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_145])).

cnf(c_0_173,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_129]),c_0_63])]),c_0_48])).

cnf(c_0_174,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_133]),c_0_36])]),c_0_50])).

cnf(c_0_175,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk3_0) = k2_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_36]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_176,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_144]),c_0_38])]),c_0_48])).

cnf(c_0_177,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk2_0) = k2_tsep_1(esk1_0,esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_63]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_178,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_131]),c_0_38]),c_0_63])]),c_0_48])).

cnf(c_0_179,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_131]),c_0_38])]),c_0_48])).

cnf(c_0_180,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk1_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_133]),c_0_32])]),c_0_24])).

cnf(c_0_181,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_152]),c_0_46]),c_0_61])]),c_0_50]),c_0_130])).

cnf(c_0_182,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,X1,X2),X3)
    | v2_struct_0(k2_tsep_1(esk3_0,X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X4,X3)
    | ~ m1_pre_topc(k2_tsep_1(esk3_0,X1,X2),X4)
    | ~ m1_pre_topc(X3,esk3_0)
    | ~ m1_pre_topc(X4,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_153]),c_0_46]),c_0_61])]),c_0_50])).

cnf(c_0_183,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_156]),c_0_156]),c_0_157]),c_0_156]),c_0_158]),c_0_60])]),c_0_159]),c_0_50])).

cnf(c_0_184,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_136]),c_0_60])]),c_0_50])).

cnf(c_0_185,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_20]),c_0_38])]),c_0_25]),c_0_48])).

cnf(c_0_186,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_36])]),c_0_50])).

cnf(c_0_187,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk3_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_165]),c_0_36])]),c_0_50]),c_0_65])).

cnf(c_0_188,negated_conjecture,
    ( r1_tsep_1(esk2_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_140]),c_0_70]),c_0_38])]),c_0_85]),c_0_48])).

cnf(c_0_189,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_129]),c_0_63])]),c_0_48])).

cnf(c_0_190,negated_conjecture,
    ( l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_152]),c_0_46])])).

cnf(c_0_191,negated_conjecture,
    ( v2_struct_0(X1)
    | l1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_167]),c_0_21])])).

cnf(c_0_192,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_193,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_167]),c_0_21]),c_0_23])])).

cnf(c_0_194,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk2_0,X1,X2),X2)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_103]),c_0_49])]),c_0_48])).

cnf(c_0_195,negated_conjecture,
    ( k2_tsep_1(esk2_0,X1,X2) = k2_tsep_1(esk2_0,X2,X1)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_63]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_196,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X4,X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X2,X3),X4)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X4,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_128]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_197,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_169])).

cnf(c_0_198,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,X2),X3) = k2_tsep_1(esk1_0,X1,k2_tsep_1(esk1_0,X2,X3))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_199,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_152]),c_0_36]),c_0_38])]),c_0_50]),c_0_48]),c_0_130])).

cnf(c_0_200,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_108]),c_0_38]),c_0_36])]),c_0_50]),c_0_48])).

cnf(c_0_201,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_172]),c_0_129]),c_0_36]),c_0_38])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_202,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_173]),c_0_130])).

cnf(c_0_203,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_174]),c_0_60])]),c_0_50])).

cnf(c_0_204,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_175]),c_0_36]),c_0_21])]),c_0_50]),c_0_24])).

cnf(c_0_205,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_155]),c_0_156]),c_0_156]),c_0_156]),c_0_135]),c_0_60])]),c_0_159]),c_0_50])).

cnf(c_0_206,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_63]),c_0_38])]),c_0_178]),c_0_48])).

cnf(c_0_207,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_131]),c_0_38]),c_0_63])]),c_0_48])).

cnf(c_0_208,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_135]),c_0_21]),c_0_23])]),c_0_24]),c_0_159])).

cnf(c_0_209,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_101]),c_0_32]),c_0_36])]),c_0_50]),c_0_24])).

cnf(c_0_210,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_152]),c_0_46]),c_0_61])]),c_0_50]),c_0_130])).

cnf(c_0_211,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_172]),c_0_152]),c_0_36]),c_0_38])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_212,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,esk3_0,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_183]),c_0_60])]),c_0_50]),c_0_184])).

cnf(c_0_213,negated_conjecture,
    ( k2_tsep_1(esk3_0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_61]),c_0_46])]),c_0_50])).

cnf(c_0_214,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_186]),c_0_36])]),c_0_50])).

cnf(c_0_215,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_187]),c_0_60])]),c_0_50])).

cnf(c_0_216,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk4_0) = k2_tsep_1(esk1_0,esk4_0,X1)
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_20]),c_0_25])).

cnf(c_0_217,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_188]),c_0_38])]),c_0_48])).

cnf(c_0_218,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_173]),c_0_129]),c_0_63])]),c_0_130]),c_0_48])).

cnf(c_0_219,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_190])).

cnf(c_0_220,negated_conjecture,
    ( v2_struct_0(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_192]),c_0_32])]),c_0_24])).

cnf(c_0_221,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_192]),c_0_32])]),c_0_24])).

cnf(c_0_222,negated_conjecture,
    ( k1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0)) = g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_152]),c_0_46]),c_0_61])]),c_0_50]),c_0_130])).

cnf(c_0_223,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk2_0,X1,esk2_0),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_63]),c_0_48])).

cnf(c_0_224,negated_conjecture,
    ( k2_tsep_1(esk2_0,X1,esk2_0) = k2_tsep_1(esk2_0,esk2_0,X1)
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_63]),c_0_48])).

cnf(c_0_225,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_197]),c_0_38])]),c_0_48])).

cnf(c_0_226,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,k2_tsep_1(esk1_0,X2,X3)),X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_128])).

cnf(c_0_227,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),X1) = k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,X1))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | r1_tsep_1(esk3_0,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_108]),c_0_38]),c_0_36])]),c_0_50]),c_0_48])).

cnf(c_0_228,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_199]),c_0_200]),c_0_38])]),c_0_130]),c_0_48])).

cnf(c_0_229,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_93]),c_0_63]),c_0_200])]),c_0_48]),c_0_130])).

cnf(c_0_230,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_129]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_231,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_155]),c_0_156]),c_0_156]),c_0_157]),c_0_156]),c_0_158]),c_0_60])]),c_0_159]),c_0_50])).

cnf(c_0_232,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_175]),c_0_36]),c_0_60])]),c_0_50])).

cnf(c_0_233,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_175]),c_0_36])]),c_0_50])).

cnf(c_0_234,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_206]),c_0_207]),c_0_135])]),c_0_178]),c_0_159])).

cnf(c_0_235,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_209]),c_0_36])]),c_0_50])).

cnf(c_0_236,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_152]),c_0_46]),c_0_61])]),c_0_50]),c_0_130])).

cnf(c_0_237,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_172]),c_0_152]),c_0_36]),c_0_38])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_238,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk3_0,esk3_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_212]),c_0_183]),c_0_152])]),c_0_184]),c_0_130])).

cnf(c_0_239,negated_conjecture,
    ( k2_tsep_1(esk3_0,X1,esk3_0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_136]),c_0_60])]),c_0_50])).

cnf(c_0_240,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_36]),c_0_21]),c_0_23])]),c_0_24]),c_0_50])).

cnf(c_0_241,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_123]),c_0_124]),c_0_124]),c_0_124]),c_0_104]),c_0_63])]),c_0_127]),c_0_48])).

cnf(c_0_242,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)
    | ~ r1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214,c_0_192]),c_0_20]),c_0_38])]),c_0_127]),c_0_48]),c_0_25])).

cnf(c_0_243,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215,c_0_216]),c_0_36])]),c_0_50])).

cnf(c_0_244,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_217]),c_0_38])]),c_0_48])).

cnf(c_0_245,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_218]),c_0_219])]),c_0_130])).

cnf(c_0_246,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk3_0,X1,k2_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_152]),c_0_46]),c_0_61])]),c_0_50]),c_0_130])).

cnf(c_0_247,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_220,c_0_200]),c_0_130])).

cnf(c_0_248,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_221,c_0_200]),c_0_130])).

cnf(c_0_249,negated_conjecture,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_222]),c_0_152]),c_0_46])]),c_0_130]),c_0_50])).

cnf(c_0_250,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk2_0)
    | m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_223]),c_0_38]),c_0_63])]),c_0_48])).

cnf(c_0_251,negated_conjecture,
    ( k2_tsep_1(esk2_0,X1,esk2_0) = k2_tsep_1(esk2_0,esk2_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_224]),c_0_48])).

cnf(c_0_252,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_225,c_0_207])]),c_0_178])).

cnf(c_0_253,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,X1,X2)),esk3_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_226]),c_0_36])]),c_0_50]),c_0_128])).

cnf(c_0_254,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X3,k2_tsep_1(esk1_0,X1,X2))
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_172]),c_0_128])).

cnf(c_0_255,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) = k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_227]),c_0_200]),c_0_38])]),c_0_130]),c_0_48]),c_0_228])).

cnf(c_0_256,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_229]),c_0_200])]),c_0_130])).

cnf(c_0_257,negated_conjecture,
    ( ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_230,c_0_172]),c_0_129]),c_0_36]),c_0_38])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_258,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_123]),c_0_124]),c_0_124]),c_0_124]),c_0_104]),c_0_63])]),c_0_127]),c_0_48])).

cnf(c_0_259,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk3_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_231]),c_0_36])]),c_0_50]),c_0_232])).

cnf(c_0_260,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_233,c_0_175]),c_0_36]),c_0_60])]),c_0_50])).

cnf(c_0_261,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_234,c_0_235]),c_0_38])]),c_0_48])).

cnf(c_0_262,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236,c_0_152]),c_0_60])]),c_0_50])).

cnf(c_0_263,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,esk3_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237,c_0_238]),c_0_183])]),c_0_184])).

cnf(c_0_264,negated_conjecture,
    ( k2_tsep_1(esk3_0,esk3_0,esk3_0) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_239]),c_0_60])]),c_0_50])).

cnf(c_0_265,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_240,c_0_65]),c_0_20])]),c_0_25])).

cnf(c_0_266,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_38]),c_0_21]),c_0_23])]),c_0_24]),c_0_48])).

cnf(c_0_267,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_200]),c_0_32]),c_0_36]),c_0_38])]),c_0_130]),c_0_50]),c_0_48]),c_0_24])).

cnf(c_0_268,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_242]),c_0_36])]),c_0_79]),c_0_50])).

cnf(c_0_269,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_155]),c_0_156]),c_0_156]),c_0_157]),c_0_156]),c_0_158]),c_0_60])]),c_0_159]),c_0_50])).

cnf(c_0_270,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk2_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_192]),c_0_20]),c_0_38])]),c_0_127]),c_0_48]),c_0_25]),c_0_99])).

cnf(c_0_271,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245,c_0_246]),c_0_222]),c_0_222]),c_0_247]),c_0_222]),c_0_248]),c_0_152])]),c_0_249]),c_0_130])).

cnf(c_0_272,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_250]),c_0_63])]),c_0_48])).

cnf(c_0_273,negated_conjecture,
    ( k2_tsep_1(esk2_0,X1,esk2_0) = k2_tsep_1(esk2_0,esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251,c_0_63]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_274,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_252,c_0_253]),c_0_36]),c_0_38])]),c_0_50]),c_0_178]),c_0_48])).

cnf(c_0_275,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) = k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254,c_0_255]),c_0_38]),c_0_36])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_276,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_256,c_0_257])).

cnf(c_0_277,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk2_0)
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258,c_0_259]),c_0_260]),c_0_104])]),c_0_232]),c_0_127])).

cnf(c_0_278,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_123]),c_0_124]),c_0_124]),c_0_124]),c_0_104]),c_0_63])]),c_0_127]),c_0_48])).

cnf(c_0_279,negated_conjecture,
    ( r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_261,c_0_101]),c_0_38]),c_0_63])]),c_0_48])).

cnf(c_0_280,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_262]),c_0_130])).

cnf(c_0_281,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_155]),c_0_156]),c_0_156]),c_0_156]),c_0_135]),c_0_60])]),c_0_159]),c_0_50])).

cnf(c_0_282,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_263,c_0_264])).

cnf(c_0_283,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237,c_0_265]),c_0_60]),c_0_200])]),c_0_50]),c_0_130])).

cnf(c_0_284,negated_conjecture,
    ( r1_tsep_1(X1,esk1_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk1_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_285,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_38]),c_0_32])]),c_0_24])).

cnf(c_0_286,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_219]),c_0_36]),c_0_38])]),c_0_50]),c_0_48]),c_0_200])]),c_0_130])).

cnf(c_0_287,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk1_0) = k2_tsep_1(esk1_0,esk1_0,X1)
    | r1_tsep_1(X1,esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_32]),c_0_24])).

cnf(c_0_288,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_267]),c_0_130])).

cnf(c_0_289,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_197]),c_0_38])]),c_0_48])).

cnf(c_0_290,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_291,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268,c_0_92]),c_0_20])]),c_0_25]),c_0_269])).

cnf(c_0_292,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_216]),c_0_20]),c_0_38])]),c_0_25]),c_0_48])).

cnf(c_0_293,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_270]),c_0_38])]),c_0_271]),c_0_48])).

cnf(c_0_294,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_272,c_0_123]),c_0_124]),c_0_124]),c_0_125]),c_0_124]),c_0_126]),c_0_63])]),c_0_127]),c_0_48])).

cnf(c_0_295,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk2_0,X1,X2),esk2_0)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_49]),c_0_48])).

cnf(c_0_296,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(esk2_0,X1,esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_273]),c_0_63]),c_0_49])]),c_0_48])).

cnf(c_0_297,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254,c_0_274]),c_0_36]),c_0_38])]),c_0_178]),c_0_50]),c_0_48])).

cnf(c_0_298,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0)) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_275,c_0_257]),c_0_276])).

cnf(c_0_299,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0)
    | ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277,c_0_101]),c_0_36]),c_0_60])]),c_0_50])).

cnf(c_0_300,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_279]),c_0_36])]),c_0_79]),c_0_50])).

cnf(c_0_301,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_265]),c_0_38])]),c_0_48])).

fof(c_0_302,plain,(
    ! [X44,X45,X46,X47] :
      ( ( ~ m1_pre_topc(X45,X47)
        | m1_pre_topc(k2_tsep_1(X44,X45,X46),k2_tsep_1(X44,X47,X46))
        | r1_tsep_1(X45,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X44)
        | v2_struct_0(X46)
        | ~ m1_pre_topc(X46,X44)
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ m1_pre_topc(X46,X47)
        | m1_pre_topc(k2_tsep_1(X44,X45,X46),k2_tsep_1(X44,X45,X47))
        | r1_tsep_1(X45,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X44)
        | v2_struct_0(X46)
        | ~ m1_pre_topc(X46,X44)
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_tmap_1])])])])])).

cnf(c_0_303,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_280,c_0_152]),c_0_46]),c_0_61])]),c_0_50])).

cnf(c_0_304,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | ~ r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_281,c_0_282]),c_0_200])]),c_0_130])).

cnf(c_0_305,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_198]),c_0_20]),c_0_36]),c_0_38])]),c_0_79]),c_0_48]),c_0_50]),c_0_25])).

cnf(c_0_306,negated_conjecture,
    ( r1_tsep_1(X1,esk1_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk1_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_32]),c_0_32])]),c_0_24])).

cnf(c_0_307,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_285]),c_0_38]),c_0_36])]),c_0_79]),c_0_48]),c_0_50])).

cnf(c_0_308,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) = k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_287]),c_0_32]),c_0_200])]),c_0_24]),c_0_130])).

cnf(c_0_309,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_288,c_0_128]),c_0_21]),c_0_23]),c_0_36]),c_0_38])]),c_0_24]),c_0_48]),c_0_50])).

cnf(c_0_310,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_289,c_0_207])]),c_0_178])).

cnf(c_0_311,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_290,c_0_291])])).

cnf(c_0_312,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_292,c_0_293])).

cnf(c_0_313,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_129]),c_0_49]),c_0_103])]),c_0_48]),c_0_130])).

cnf(c_0_314,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk2_0,esk2_0,esk2_0),X1)
    | v2_struct_0(k2_tsep_1(esk2_0,esk2_0,esk2_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X2,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_294]),c_0_49]),c_0_103])]),c_0_48])).

cnf(c_0_315,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,X1),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_295,c_0_273]),c_0_63])]),c_0_48])).

cnf(c_0_316,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk2_0,esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_296,c_0_273]),c_0_63])]),c_0_48])).

cnf(c_0_317,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_297,c_0_298])).

cnf(c_0_318,negated_conjecture,
    ( ~ r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_299]),c_0_38])]),c_0_300]),c_0_48])).

cnf(c_0_319,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_320,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_216]),c_0_38])]),c_0_48])).

cnf(c_0_321,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_302])).

cnf(c_0_322,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_216]),c_0_200])]),c_0_130])).

cnf(c_0_323,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_303,c_0_304]),c_0_219]),c_0_152])]),c_0_130])).

cnf(c_0_324,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_305,c_0_291])).

cnf(c_0_325,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk1_0) = k2_tsep_1(esk1_0,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_306,c_0_92]),c_0_36]),c_0_32])]),c_0_307]),c_0_50]),c_0_24])).

cnf(c_0_326,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) = k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_306,c_0_308]),c_0_200])]),c_0_130])).

cnf(c_0_327,negated_conjecture,
    ( ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_309,c_0_172]),c_0_200]),c_0_36]),c_0_38])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_328,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_310,c_0_176]),c_0_178])).

cnf(c_0_329,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_311,c_0_312])])).

cnf(c_0_330,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_291]),c_0_20]),c_0_36])]),c_0_50]),c_0_25])).

cnf(c_0_331,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_291]),c_0_20]),c_0_36]),c_0_21])]),c_0_25]),c_0_50]),c_0_24])).

cnf(c_0_332,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_123]),c_0_124]),c_0_124]),c_0_124]),c_0_104]),c_0_63])]),c_0_127]),c_0_48])).

cnf(c_0_333,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_231]),c_0_36])]),c_0_50]),c_0_232])).

cnf(c_0_334,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_172]),c_0_129]),c_0_36]),c_0_38])]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_335,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk2_0,esk2_0,esk2_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_314,c_0_315]),c_0_63])]),c_0_316]),c_0_48])).

cnf(c_0_336,negated_conjecture,
    ( k2_tsep_1(esk2_0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_103]),c_0_49])]),c_0_48])).

cnf(c_0_337,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_101]),c_0_38]),c_0_63])]),c_0_318]),c_0_48])).

cnf(c_0_338,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_276]),c_0_38]),c_0_200]),c_0_21])]),c_0_48]),c_0_130]),c_0_24])).

cnf(c_0_339,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_319,c_0_320])).

cnf(c_0_340,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_320]),c_0_20]),c_0_38])]),c_0_48]),c_0_25])).

cnf(c_0_341,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_320]),c_0_20]),c_0_38]),c_0_21])]),c_0_25]),c_0_48]),c_0_24])).

cnf(c_0_342,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),k2_tsep_1(esk1_0,X1,X3))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321,c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_343,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_302])).

cnf(c_0_344,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_322,c_0_323])).

cnf(c_0_345,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) = k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_324,c_0_323])).

cnf(c_0_346,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk1_0,esk3_0) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_325]),c_0_32]),c_0_36])]),c_0_50]),c_0_24])).

cnf(c_0_347,negated_conjecture,
    ( k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) = k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_326,c_0_327])).

cnf(c_0_348,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_328,c_0_329]),c_0_330])]),c_0_331])).

cnf(c_0_349,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk2_0)
    | ~ r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_332,c_0_333]),c_0_260]),c_0_104])]),c_0_232]),c_0_127])).

cnf(c_0_350,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk2_0,esk2_0,esk2_0))
    | ~ r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_334,c_0_335]),c_0_294]),c_0_129])]),c_0_316]),c_0_130])).

cnf(c_0_351,negated_conjecture,
    ( k2_tsep_1(esk2_0,X1,esk2_0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_336,c_0_273]),c_0_63])]),c_0_48])).

cnf(c_0_352,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_20]),c_0_21]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_353,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_337]),c_0_36]),c_0_200]),c_0_38])]),c_0_338]),c_0_130]),c_0_48]),c_0_50])).

cnf(c_0_354,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_339]),c_0_340]),c_0_341])).

cnf(c_0_355,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_312]),c_0_20]),c_0_38])]),c_0_48]),c_0_25])).

cnf(c_0_356,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_312]),c_0_20]),c_0_38]),c_0_21])]),c_0_25]),c_0_48]),c_0_24])).

cnf(c_0_357,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),k2_tsep_1(esk1_0,esk3_0,X2))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_342,c_0_36]),c_0_50])).

cnf(c_0_358,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),k2_tsep_1(esk1_0,X3,X2))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_343,c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_359,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0)) = k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_344,c_0_345])).

cnf(c_0_360,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk4_0,esk3_0) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_269]),c_0_20]),c_0_36])]),c_0_50]),c_0_25]),c_0_65])).

cnf(c_0_361,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_327,c_0_198]),c_0_325]),c_0_346]),c_0_32]),c_0_36]),c_0_38])]),c_0_79]),c_0_48]),c_0_50]),c_0_24]),c_0_347])).

cnf(c_0_362,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_348,c_0_101]),c_0_38]),c_0_63])]),c_0_48])).

cnf(c_0_363,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0)
    | ~ r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_349,c_0_101]),c_0_36]),c_0_60])]),c_0_50])).

cnf(c_0_364,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk2_0,esk2_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_350]),c_0_294])]),c_0_316])).

cnf(c_0_365,negated_conjecture,
    ( k2_tsep_1(esk2_0,esk2_0,esk2_0) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273,c_0_351]),c_0_63])]),c_0_48])).

cnf(c_0_366,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_352,c_0_30]),c_0_20])]),c_0_25])).

cnf(c_0_367,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_353,c_0_354]),c_0_355])]),c_0_356])).

cnf(c_0_368,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_357,c_0_20]),c_0_25]),c_0_291])).

cnf(c_0_369,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),k2_tsep_1(esk1_0,X2,esk2_0))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_358,c_0_38]),c_0_48])).

cnf(c_0_370,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) = k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359,c_0_360]),c_0_361])).

cnf(c_0_371,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) = g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_347]),c_0_32]),c_0_200])]),c_0_130]),c_0_24])).

cnf(c_0_372,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_78]),c_0_60]),c_0_200])]),c_0_50]),c_0_130])).

cnf(c_0_373,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_362]),c_0_355])]),c_0_356])).

cnf(c_0_374,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_363]),c_0_38])]),c_0_300]),c_0_48])).

cnf(c_0_375,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_364,c_0_365])).

cnf(c_0_376,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,k2_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_200]),c_0_130])).

cnf(c_0_377,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_366,c_0_88]),c_0_38]),c_0_20])]),c_0_48]),c_0_25])).

cnf(c_0_378,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_88]),c_0_20])]),c_0_25])).

cnf(c_0_379,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254,c_0_367]),c_0_355]),c_0_200]),c_0_38])]),c_0_338]),c_0_356]),c_0_48]),c_0_130])).

cnf(c_0_380,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_108]),c_0_38]),c_0_36])]),c_0_48]),c_0_50]),c_0_130])).

cnf(c_0_381,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_368]),c_0_108]),c_0_36]),c_0_38])]),c_0_79]),c_0_50]),c_0_48])).

cnf(c_0_382,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_369,c_0_20]),c_0_25])).

cnf(c_0_383,plain,
    ( m1_pre_topc(X3,X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_tsep_1(X1,X2,X3) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_384,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) = g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_370,c_0_371])).

cnf(c_0_385,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_303,c_0_372]),c_0_219]),c_0_152])]),c_0_130])).

cnf(c_0_386,negated_conjecture,
    ( r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_373,c_0_101]),c_0_20]),c_0_38])]),c_0_374]),c_0_48]),c_0_25])).

cnf(c_0_387,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | ~ r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258,c_0_375]),c_0_200])]),c_0_130])).

cnf(c_0_388,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_376]),c_0_200]),c_0_38])]),c_0_130]),c_0_48])).

cnf(c_0_389,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_377]),c_0_25]),c_0_48]),c_0_378])).

cnf(c_0_390,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_379]),c_0_356]),c_0_338])).

cnf(c_0_391,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_380,c_0_381]),c_0_330])]),c_0_331])).

cnf(c_0_392,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257,c_0_382]),c_0_200])]),c_0_130]),c_0_276])).

cnf(c_0_393,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_383,c_0_384]),c_0_200]),c_0_20]),c_0_21]),c_0_23])]),c_0_130]),c_0_25]),c_0_24]),c_0_385])).

cnf(c_0_394,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_386]),c_0_330])]),c_0_331])).

cnf(c_0_395,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_257,c_0_387])).

cnf(c_0_396,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[c_0_388,c_0_257])).

cnf(c_0_397,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_389,c_0_38]),c_0_20]),c_0_21]),c_0_23])]),c_0_24])).

cnf(c_0_398,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_390,c_0_391,c_0_392,c_0_393,c_0_394,c_0_395,c_0_48,c_0_396,c_0_397,c_0_103,c_0_49,c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 50.22/50.47  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 50.22/50.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 50.22/50.47  #
% 50.22/50.47  # Preprocessing time       : 0.030 s
% 50.22/50.47  # Presaturation interreduction done
% 50.22/50.47  # SatCheck found unsatisfiable ground set
% 50.22/50.47  
% 50.22/50.47  # Proof found!
% 50.22/50.47  # SZS status Theorem
% 50.22/50.47  # SZS output start CNFRefutation
% 50.22/50.47  fof(t34_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X4,X3),X2))&~(r1_tsep_1(k2_tsep_1(X1,X3,X4),X2))))&(m1_pre_topc(X3,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X2,X4),X3))&~(r1_tsep_1(k2_tsep_1(X1,X4,X2),X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tmap_1)).
% 50.22/50.47  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 50.22/50.47  fof(t23_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 50.22/50.47  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 50.22/50.47  fof(t30_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>(m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)&m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tsep_1)).
% 50.22/50.47  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 50.22/50.47  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 50.22/50.47  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 50.22/50.47  fof(t22_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)=>(~(r1_tsep_1(X2,X3))&~(r1_tsep_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 50.22/50.47  fof(t29_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((~(r1_tsep_1(X2,X3))=>k2_tsep_1(X1,X2,X3)=k2_tsep_1(X1,X3,X2))&(((~(r1_tsep_1(X2,X3))&~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X2,k2_tsep_1(X1,X3,X4)))))=>k2_tsep_1(X1,k2_tsep_1(X1,X2,X3),X4)=k2_tsep_1(X1,X2,k2_tsep_1(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tsep_1)).
% 50.22/50.47  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 50.22/50.47  fof(t31_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>((((m1_pre_topc(X2,X3)=>k2_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&(k2_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>m1_pre_topc(X2,X3)))&(m1_pre_topc(X3,X2)=>k2_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))&(k2_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>m1_pre_topc(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tsep_1)).
% 50.22/50.47  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 50.22/50.47  fof(t32_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X3)))&(m1_pre_topc(X3,X4)=>m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tmap_1)).
% 50.22/50.47  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X4,X3),X2))&~(r1_tsep_1(k2_tsep_1(X1,X3,X4),X2))))&(m1_pre_topc(X3,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X2,X4),X3))&~(r1_tsep_1(k2_tsep_1(X1,X4,X2),X3))))))))))), inference(assume_negation,[status(cth)],[t34_tmap_1])).
% 50.22/50.47  fof(c_0_15, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 50.22/50.47  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(((m1_pre_topc(esk3_0,esk4_0)|m1_pre_topc(esk2_0,esk4_0))&(r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)))&((m1_pre_topc(esk3_0,esk4_0)|(r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)))&(r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|(r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 50.22/50.47  fof(c_0_17, plain, ![X22, X23, X24, X25]:(((~r1_tsep_1(X24,X25)|r1_tsep_1(X23,X25)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_tsep_1(X25,X24)|r1_tsep_1(X23,X25)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))))&((~r1_tsep_1(X24,X25)|r1_tsep_1(X25,X23)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_tsep_1(X25,X24)|r1_tsep_1(X25,X23)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).
% 50.22/50.47  fof(c_0_18, plain, ![X37]:(~l1_pre_topc(X37)|m1_pre_topc(X37,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 50.22/50.47  cnf(c_0_19, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 50.22/50.47  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_22, plain, (r1_tsep_1(X3,X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 50.22/50.47  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_26, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 50.22/50.47  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 50.22/50.47  cnf(c_0_28, plain, (r1_tsep_1(X3,X2)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 50.22/50.47  cnf(c_0_29, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21]), c_0_23])]), c_0_24]), c_0_25])).
% 50.22/50.47  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 50.22/50.47  cnf(c_0_31, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_21]), c_0_23])]), c_0_24]), c_0_25])).
% 50.22/50.47  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 50.22/50.47  fof(c_0_33, plain, ![X38, X39, X40]:((m1_pre_topc(k2_tsep_1(X38,X39,X40),X39)|r1_tsep_1(X39,X40)|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(m1_pre_topc(k2_tsep_1(X38,X39,X40),X40)|r1_tsep_1(X39,X40)|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).
% 50.22/50.47  fof(c_0_34, plain, ![X10, X11, X12]:(((~v2_struct_0(k1_tsep_1(X10,X11,X12))|(v2_struct_0(X10)|~l1_pre_topc(X10)|v2_struct_0(X11)|~m1_pre_topc(X11,X10)|v2_struct_0(X12)|~m1_pre_topc(X12,X10)))&(v1_pre_topc(k1_tsep_1(X10,X11,X12))|(v2_struct_0(X10)|~l1_pre_topc(X10)|v2_struct_0(X11)|~m1_pre_topc(X11,X10)|v2_struct_0(X12)|~m1_pre_topc(X12,X10))))&(m1_pre_topc(k1_tsep_1(X10,X11,X12),X10)|(v2_struct_0(X10)|~l1_pre_topc(X10)|v2_struct_0(X11)|~m1_pre_topc(X11,X10)|v2_struct_0(X12)|~m1_pre_topc(X12,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 50.22/50.47  fof(c_0_35, plain, ![X26, X27]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X26)|k1_tsep_1(X26,X27,X27)=g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 50.22/50.47  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  fof(c_0_37, plain, ![X6, X7]:(~v2_pre_topc(X6)|~l1_pre_topc(X6)|(~m1_pre_topc(X7,X6)|v2_pre_topc(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 50.22/50.47  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  fof(c_0_39, plain, ![X16, X17, X18]:((~r1_tsep_1(X17,X18)|~m1_pre_topc(X17,X18)|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r1_tsep_1(X18,X17)|~m1_pre_topc(X17,X18)|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).
% 50.22/50.47  cnf(c_0_40, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_41, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(X1)|~r1_tsep_1(esk1_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_42, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 50.22/50.47  cnf(c_0_43, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 50.22/50.47  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 50.22/50.47  fof(c_0_45, plain, ![X33, X34, X35, X36]:((r1_tsep_1(X34,X35)|k2_tsep_1(X33,X34,X35)=k2_tsep_1(X33,X35,X34)|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&((r1_tsep_1(X34,X35)|r1_tsep_1(k2_tsep_1(X33,X34,X35),X36)|k2_tsep_1(X33,k2_tsep_1(X33,X34,X35),X36)=k2_tsep_1(X33,X34,k2_tsep_1(X33,X35,X36))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(r1_tsep_1(X35,X36)|r1_tsep_1(X34,k2_tsep_1(X33,X35,X36))|k2_tsep_1(X33,k2_tsep_1(X33,X34,X35),X36)=k2_tsep_1(X33,X34,k2_tsep_1(X33,X35,X36))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~m1_pre_topc(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_tsep_1])])])])])).
% 50.22/50.47  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_36]), c_0_21])])).
% 50.22/50.47  cnf(c_0_47, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 50.22/50.47  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_49, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_38]), c_0_21])])).
% 50.22/50.47  cnf(c_0_50, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 50.22/50.47  cnf(c_0_52, negated_conjecture, (r1_tsep_1(esk4_0,esk4_0)|~r1_tsep_1(esk1_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_53, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  fof(c_0_54, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(v2_struct_0(X20)|~m1_pre_topc(X20,X19)|(v2_struct_0(X21)|~m1_pre_topc(X21,X19)|m1_pre_topc(X20,k1_tsep_1(X19,X20,X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 50.22/50.47  cnf(c_0_55, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k1_tsep_1(esk1_0,X1,X2),esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_24])).
% 50.22/50.47  cnf(c_0_56, negated_conjecture, (k1_tsep_1(esk1_0,esk4_0,esk4_0)=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_20]), c_0_21]), c_0_23])]), c_0_25]), c_0_24])).
% 50.22/50.47  fof(c_0_57, plain, ![X41, X42, X43]:((((~m1_pre_topc(X42,X43)|k2_tsep_1(X41,X42,X43)=g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))|r1_tsep_1(X42,X43)|(v2_struct_0(X43)|~m1_pre_topc(X43,X41))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(k2_tsep_1(X41,X42,X43)!=g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))|m1_pre_topc(X42,X43)|r1_tsep_1(X42,X43)|(v2_struct_0(X43)|~m1_pre_topc(X43,X41))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41))))&(~m1_pre_topc(X43,X42)|k2_tsep_1(X41,X42,X43)=g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43))|r1_tsep_1(X42,X43)|(v2_struct_0(X43)|~m1_pre_topc(X43,X41))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41))))&(k2_tsep_1(X41,X42,X43)!=g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43))|m1_pre_topc(X43,X42)|r1_tsep_1(X42,X43)|(v2_struct_0(X43)|~m1_pre_topc(X43,X41))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_tsep_1])])])])])).
% 50.22/50.47  cnf(c_0_58, plain, (r1_tsep_1(X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 50.22/50.47  cnf(c_0_59, plain, (r1_tsep_1(X1,X2)|k2_tsep_1(X3,X1,X2)=k2_tsep_1(X3,X2,X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 50.22/50.47  cnf(c_0_60, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_46])).
% 50.22/50.47  cnf(c_0_61, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_36]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_38]), c_0_21]), c_0_23])]), c_0_24]), c_0_48])).
% 50.22/50.47  cnf(c_0_63, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_49])).
% 50.22/50.47  cnf(c_0_64, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_21]), c_0_23])]), c_0_24]), c_0_50])).
% 50.22/50.47  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)|m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_66, negated_conjecture, (v2_struct_0(X1)|~r1_tsep_1(esk1_0,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_30])]), c_0_25])).
% 50.22/50.47  cnf(c_0_67, negated_conjecture, (r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk4_0),esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_20]), c_0_25])).
% 50.22/50.47  cnf(c_0_68, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 50.22/50.47  cnf(c_0_69, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_20]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_70, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_71, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 50.22/50.47  cnf(c_0_72, plain, (k2_tsep_1(X3,X2,X1)=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|r1_tsep_1(X2,X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 50.22/50.47  cnf(c_0_73, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_38]), c_0_21]), c_0_23])]), c_0_24]), c_0_48])).
% 50.22/50.47  cnf(c_0_74, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 50.22/50.47  cnf(c_0_75, negated_conjecture, (k2_tsep_1(esk1_0,X1,X2)=k2_tsep_1(esk1_0,X2,X1)|r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_20]), c_0_21]), c_0_23])]), c_0_25]), c_0_24])).
% 50.22/50.47  cnf(c_0_76, negated_conjecture, (k2_tsep_1(esk3_0,X1,X2)=k2_tsep_1(esk3_0,X2,X1)|r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_46]), c_0_61])]), c_0_50])).
% 50.22/50.47  cnf(c_0_77, negated_conjecture, (r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_78, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_79, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_80, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk1_0,esk4_0),esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_81, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk4_0,X1,esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_30]), c_0_27]), c_0_69])]), c_0_25])).
% 50.22/50.47  cnf(c_0_82, negated_conjecture, (k1_tsep_1(esk4_0,esk4_0,esk4_0)=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_27]), c_0_69])]), c_0_25])).
% 50.22/50.47  cnf(c_0_83, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_70]), c_0_21])])).
% 50.22/50.47  cnf(c_0_84, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_70]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_85, negated_conjecture, (~v2_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_56]), c_0_20]), c_0_21])]), c_0_25]), c_0_24])).
% 50.22/50.47  cnf(c_0_86, plain, (k2_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_72, c_0_51])).
% 50.22/50.47  cnf(c_0_87, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_63]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_88, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_38]), c_0_48])).
% 50.22/50.47  cnf(c_0_89, negated_conjecture, (k1_tsep_1(esk1_0,esk2_0,esk2_0)=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_21]), c_0_23])]), c_0_48]), c_0_24])).
% 50.22/50.47  fof(c_0_90, plain, ![X13, X14, X15]:(((~v2_struct_0(k2_tsep_1(X13,X14,X15))|(v2_struct_0(X13)|~l1_pre_topc(X13)|v2_struct_0(X14)|~m1_pre_topc(X14,X13)|v2_struct_0(X15)|~m1_pre_topc(X15,X13)))&(v1_pre_topc(k2_tsep_1(X13,X14,X15))|(v2_struct_0(X13)|~l1_pre_topc(X13)|v2_struct_0(X14)|~m1_pre_topc(X14,X13)|v2_struct_0(X15)|~m1_pre_topc(X15,X13))))&(m1_pre_topc(k2_tsep_1(X13,X14,X15),X13)|(v2_struct_0(X13)|~l1_pre_topc(X13)|v2_struct_0(X14)|~m1_pre_topc(X14,X13)|v2_struct_0(X15)|~m1_pre_topc(X15,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 50.22/50.47  cnf(c_0_91, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  cnf(c_0_92, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk3_0)=k2_tsep_1(esk1_0,esk3_0,X1)|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_36]), c_0_50])).
% 50.22/50.47  cnf(c_0_93, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk2_0)=k2_tsep_1(esk1_0,esk2_0,X1)|r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_38]), c_0_48])).
% 50.22/50.47  cnf(c_0_94, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_36]), c_0_21]), c_0_23])]), c_0_24]), c_0_50])).
% 50.22/50.47  cnf(c_0_95, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk3_0,X1,X2),X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_61]), c_0_46])]), c_0_50])).
% 50.22/50.47  cnf(c_0_96, plain, (v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 50.22/50.47  cnf(c_0_97, negated_conjecture, (k2_tsep_1(esk3_0,X1,esk3_0)=k2_tsep_1(esk3_0,esk3_0,X1)|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_60]), c_0_50])).
% 50.22/50.47  cnf(c_0_98, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk4_0),esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(spm,[status(thm)],[c_0_40, c_0_67])).
% 50.22/50.47  cnf(c_0_99, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_36]), c_0_38])]), c_0_79]), c_0_50]), c_0_48])).
% 50.22/50.47  cnf(c_0_100, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk1_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_82]), c_0_83]), c_0_82]), c_0_84]), c_0_30])]), c_0_85]), c_0_25])).
% 50.22/50.47  cnf(c_0_101, negated_conjecture, (k2_tsep_1(esk1_0,X1,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  cnf(c_0_102, negated_conjecture, (r1_tsep_1(esk2_0,esk2_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_103, negated_conjecture, (v2_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_104, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_89]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_105, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 50.22/50.47  cnf(c_0_106, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_36]), c_0_50])).
% 50.22/50.47  cnf(c_0_107, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 50.22/50.47  cnf(c_0_108, negated_conjecture, (k2_tsep_1(esk1_0,esk3_0,esk2_0)=k2_tsep_1(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_92]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_109, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk2_0)=k2_tsep_1(esk1_0,esk2_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_93]), c_0_48])).
% 50.22/50.47  cnf(c_0_110, negated_conjecture, (r1_tsep_1(esk2_0,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_21]), c_0_23])]), c_0_24]), c_0_48])).
% 50.22/50.47  cnf(c_0_111, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_60]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_112, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk3_0,X1,esk3_0),esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_60]), c_0_50])).
% 50.22/50.47  cnf(c_0_113, negated_conjecture, (k1_tsep_1(esk1_0,esk3_0,esk3_0)=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_21]), c_0_23])]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_114, negated_conjecture, (k2_tsep_1(esk3_0,X1,esk3_0)=k2_tsep_1(esk3_0,esk3_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_50])).
% 50.22/50.47  cnf(c_0_115, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_98]), c_0_20]), c_0_38])]), c_0_25]), c_0_48])).
% 50.22/50.47  cnf(c_0_116, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0)|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_98]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_117, plain, (r1_tsep_1(X1,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 50.22/50.47  cnf(c_0_118, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_36]), c_0_21]), c_0_23])]), c_0_24]), c_0_50])).
% 50.22/50.47  cnf(c_0_119, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_70]), c_0_21]), c_0_23])]), c_0_24]), c_0_85])).
% 50.22/50.47  cnf(c_0_120, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_32]), c_0_20])]), c_0_25]), c_0_24])).
% 50.22/50.47  cnf(c_0_121, negated_conjecture, (r1_tsep_1(X1,esk1_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_32]), c_0_24])).
% 50.22/50.47  cnf(c_0_122, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk2_0)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_102]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_123, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk2_0,X1,esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_63]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_124, negated_conjecture, (k1_tsep_1(esk2_0,esk2_0,esk2_0)=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_63]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_125, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_104]), c_0_21])])).
% 50.22/50.47  cnf(c_0_126, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_104]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_127, negated_conjecture, (~v2_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_89]), c_0_38]), c_0_21])]), c_0_48]), c_0_24])).
% 50.22/50.47  cnf(c_0_128, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_21]), c_0_24])).
% 50.22/50.47  cnf(c_0_129, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_106]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_130, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_38]), c_0_36]), c_0_21])]), c_0_48]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_131, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk2_0)=k2_tsep_1(esk1_0,esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_38]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_132, negated_conjecture, (r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~r1_tsep_1(esk1_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_38]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_133, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_36]), c_0_50])).
% 50.22/50.47  cnf(c_0_134, negated_conjecture, (r1_tsep_1(esk3_0,esk3_0)|m1_pre_topc(k2_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_36]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_135, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_113]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_136, negated_conjecture, (k2_tsep_1(esk3_0,X1,esk3_0)=k2_tsep_1(esk3_0,esk3_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_60]), c_0_46]), c_0_61])]), c_0_50])).
% 50.22/50.47  cnf(c_0_137, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_115]), c_0_25]), c_0_48]), c_0_116])).
% 50.22/50.47  cnf(c_0_138, negated_conjecture, (r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_20]), c_0_21]), c_0_23])]), c_0_24]), c_0_25])).
% 50.22/50.47  cnf(c_0_139, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_60]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_140, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X1)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_141, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_65]), c_0_25]), c_0_50]), c_0_27]), c_0_69])])).
% 50.22/50.47  cnf(c_0_142, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0),esk1_0)|~m1_pre_topc(esk1_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_121]), c_0_24])).
% 50.22/50.47  cnf(c_0_143, plain, (k2_tsep_1(X3,X1,X2)=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 50.22/50.47  cnf(c_0_144, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124]), c_0_124]), c_0_125]), c_0_124]), c_0_126]), c_0_63])]), c_0_127]), c_0_48])).
% 50.22/50.47  cnf(c_0_145, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|l1_pre_topc(k2_tsep_1(esk1_0,X2,X1))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_128]), c_0_21])])).
% 50.22/50.47  cnf(c_0_146, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_129]), c_0_49]), c_0_103])]), c_0_48]), c_0_130])).
% 50.22/50.47  cnf(c_0_147, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk3_0)=k2_tsep_1(esk1_0,esk3_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_92]), c_0_50])).
% 50.22/50.47  cnf(c_0_148, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,X3))|v2_struct_0(k2_tsep_1(esk1_0,X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|~r1_tsep_1(X1,X4)|~m1_pre_topc(k2_tsep_1(esk1_0,X2,X3),X4)|~m1_pre_topc(X4,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_128]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_149, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk2_0)=k2_tsep_1(esk1_0,esk2_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_93]), c_0_48])).
% 50.22/50.47  cnf(c_0_150, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k2_tsep_1(esk1_0,X1,esk2_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(esk2_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_131]), c_0_38]), c_0_21])]), c_0_48]), c_0_24])).
% 50.22/50.47  cnf(c_0_151, negated_conjecture, (~r1_tsep_1(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_132]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_152, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_133]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_153, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk3_0,X1,X2),esk3_0)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_46]), c_0_50])).
% 50.22/50.47  cnf(c_0_154, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_134]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_155, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk3_0,X1,esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_60]), c_0_46]), c_0_61])]), c_0_50])).
% 50.22/50.47  cnf(c_0_156, negated_conjecture, (k1_tsep_1(esk3_0,esk3_0,esk3_0)=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_60]), c_0_46]), c_0_61])]), c_0_50])).
% 50.22/50.47  cnf(c_0_157, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_135]), c_0_21])])).
% 50.22/50.47  cnf(c_0_158, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_135]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_159, negated_conjecture, (~v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_113]), c_0_36]), c_0_21])]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_160, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k2_tsep_1(esk3_0,X1,esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_136]), c_0_60]), c_0_46])]), c_0_50])).
% 50.22/50.47  cnf(c_0_161, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)|v2_struct_0(k2_tsep_1(esk1_0,X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X3,X4)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X4)|~m1_pre_topc(X4,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_128]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_162, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_38]), c_0_20]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_163, negated_conjecture, (r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~r1_tsep_1(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_81]), c_0_82]), c_0_82]), c_0_82]), c_0_70]), c_0_30])]), c_0_85]), c_0_25])).
% 50.22/50.47  cnf(c_0_164, negated_conjecture, (r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~r1_tsep_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_70]), c_0_36])]), c_0_85]), c_0_50])).
% 50.22/50.47  cnf(c_0_165, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_65]), c_0_30])]), c_0_25])).
% 50.22/50.47  cnf(c_0_166, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X2,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_129]), c_0_49]), c_0_103])]), c_0_48]), c_0_130])).
% 50.22/50.47  cnf(c_0_167, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_32]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_168, plain, (k2_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_143, c_0_96])).
% 50.22/50.47  cnf(c_0_169, negated_conjecture, (l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_144]), c_0_49])])).
% 50.22/50.47  cnf(c_0_170, plain, (r1_tsep_1(X1,X2)|r1_tsep_1(k2_tsep_1(X3,X1,X2),X4)|k2_tsep_1(X3,k2_tsep_1(X3,X1,X2),X4)=k2_tsep_1(X3,X1,k2_tsep_1(X3,X2,X4))|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 50.22/50.47  cnf(c_0_171, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)|v2_struct_0(k2_tsep_1(esk1_0,X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|~r1_tsep_1(X4,X3)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),X4)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X4,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_128]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_172, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),k2_tsep_1(esk1_0,X1,X2))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_145])).
% 50.22/50.47  cnf(c_0_173, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_129]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_174, negated_conjecture, (r1_tsep_1(esk3_0,esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_133]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_175, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk3_0)=k2_tsep_1(esk1_0,esk3_0,X1)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_36]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_176, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_144]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_177, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk2_0)=k2_tsep_1(esk1_0,esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_63]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_178, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_131]), c_0_38]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_179, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(esk2_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_131]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_180, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk1_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_133]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_181, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_152]), c_0_46]), c_0_61])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_182, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk3_0,X1,X2),X3)|v2_struct_0(k2_tsep_1(esk3_0,X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|~r1_tsep_1(X4,X3)|~m1_pre_topc(k2_tsep_1(esk3_0,X1,X2),X4)|~m1_pre_topc(X3,esk3_0)|~m1_pre_topc(X4,esk3_0)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_153]), c_0_46]), c_0_61])]), c_0_50])).
% 50.22/50.47  cnf(c_0_183, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_156]), c_0_156]), c_0_157]), c_0_156]), c_0_158]), c_0_60])]), c_0_159]), c_0_50])).
% 50.22/50.47  cnf(c_0_184, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_136]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_185, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_20]), c_0_38])]), c_0_25]), c_0_48])).
% 50.22/50.47  cnf(c_0_186, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~r1_tsep_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_187, negated_conjecture, (r1_tsep_1(esk3_0,esk3_0)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_165]), c_0_36])]), c_0_50]), c_0_65])).
% 50.22/50.47  cnf(c_0_188, negated_conjecture, (r1_tsep_1(esk2_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_140]), c_0_70]), c_0_38])]), c_0_85]), c_0_48])).
% 50.22/50.47  cnf(c_0_189, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_129]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_190, negated_conjecture, (l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_152]), c_0_46])])).
% 50.22/50.47  cnf(c_0_191, negated_conjecture, (v2_struct_0(X1)|l1_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_167]), c_0_21])])).
% 50.22/50.47  cnf(c_0_192, negated_conjecture, (k2_tsep_1(esk1_0,X1,X2)=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  cnf(c_0_193, negated_conjecture, (v2_struct_0(X1)|v2_pre_topc(k2_tsep_1(esk1_0,X1,esk1_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_167]), c_0_21]), c_0_23])])).
% 50.22/50.47  cnf(c_0_194, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk2_0,X1,X2),X2)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_103]), c_0_49])]), c_0_48])).
% 50.22/50.47  cnf(c_0_195, negated_conjecture, (k2_tsep_1(esk2_0,X1,X2)=k2_tsep_1(esk2_0,X2,X1)|r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_63]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_196, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,X3))|v2_struct_0(k2_tsep_1(esk1_0,X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X1)|~r1_tsep_1(X4,X1)|~m1_pre_topc(k2_tsep_1(esk1_0,X2,X3),X4)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X4,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_128]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_197, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_169])).
% 50.22/50.47  cnf(c_0_198, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,X2),X3)=k2_tsep_1(esk1_0,X1,k2_tsep_1(esk1_0,X2,X3))|r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)|r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  cnf(c_0_199, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|v2_struct_0(X1)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_152]), c_0_36]), c_0_38])]), c_0_50]), c_0_48]), c_0_130])).
% 50.22/50.47  cnf(c_0_200, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_108]), c_0_38]), c_0_36])]), c_0_50]), c_0_48])).
% 50.22/50.47  cnf(c_0_201, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_172]), c_0_129]), c_0_36]), c_0_38])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_202, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_173]), c_0_130])).
% 50.22/50.47  cnf(c_0_203, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_174]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_204, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(esk3_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_175]), c_0_36]), c_0_21])]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_205, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_155]), c_0_156]), c_0_156]), c_0_156]), c_0_135]), c_0_60])]), c_0_159]), c_0_50])).
% 50.22/50.47  cnf(c_0_206, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_63]), c_0_38])]), c_0_178]), c_0_48])).
% 50.22/50.47  cnf(c_0_207, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_131]), c_0_38]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_208, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_135]), c_0_21]), c_0_23])]), c_0_24]), c_0_159])).
% 50.22/50.47  cnf(c_0_209, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_101]), c_0_32]), c_0_36])]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_210, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X2,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_152]), c_0_46]), c_0_61])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_211, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|v2_struct_0(X1)|~r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_172]), c_0_152]), c_0_36]), c_0_38])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_212, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk3_0,esk3_0,esk3_0),X1)|v2_struct_0(X1)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_183]), c_0_60])]), c_0_50]), c_0_184])).
% 50.22/50.47  cnf(c_0_213, negated_conjecture, (k2_tsep_1(esk3_0,X1,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_61]), c_0_46])]), c_0_50])).
% 50.22/50.47  cnf(c_0_214, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_186]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_215, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_187]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_216, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk4_0)=k2_tsep_1(esk1_0,esk4_0,X1)|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_20]), c_0_25])).
% 50.22/50.47  cnf(c_0_217, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_188]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_218, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_173]), c_0_129]), c_0_63])]), c_0_130]), c_0_48])).
% 50.22/50.47  cnf(c_0_219, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_190])).
% 50.22/50.47  cnf(c_0_220, negated_conjecture, (v2_struct_0(X1)|l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_192]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_221, negated_conjecture, (v2_struct_0(X1)|v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_192]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_222, negated_conjecture, (k1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))=g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_152]), c_0_46]), c_0_61])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_223, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk2_0,X1,esk2_0),esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_63]), c_0_48])).
% 50.22/50.47  cnf(c_0_224, negated_conjecture, (k2_tsep_1(esk2_0,X1,esk2_0)=k2_tsep_1(esk2_0,esk2_0,X1)|r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_63]), c_0_48])).
% 50.22/50.47  cnf(c_0_225, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_197]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_226, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,X3))|v2_struct_0(k2_tsep_1(esk1_0,X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,k2_tsep_1(esk1_0,X2,X3)),X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(spm,[status(thm)],[c_0_91, c_0_128])).
% 50.22/50.47  cnf(c_0_227, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)=k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,X1))|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|r1_tsep_1(esk3_0,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_108]), c_0_38]), c_0_36])]), c_0_50]), c_0_48])).
% 50.22/50.47  cnf(c_0_228, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_199]), c_0_200]), c_0_38])]), c_0_130]), c_0_48])).
% 50.22/50.47  cnf(c_0_229, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_93]), c_0_63]), c_0_200])]), c_0_48]), c_0_130])).
% 50.22/50.47  cnf(c_0_230, negated_conjecture, (v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_129]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_231, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_155]), c_0_156]), c_0_156]), c_0_157]), c_0_156]), c_0_158]), c_0_60])]), c_0_159]), c_0_50])).
% 50.22/50.47  cnf(c_0_232, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204, c_0_175]), c_0_36]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_233, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_175]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_234, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_206]), c_0_207]), c_0_135])]), c_0_178]), c_0_159])).
% 50.22/50.47  cnf(c_0_235, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)|v2_struct_0(X1)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208, c_0_209]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_236, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_152]), c_0_46]), c_0_61])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_237, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210, c_0_172]), c_0_152]), c_0_36]), c_0_38])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_238, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk3_0,esk3_0,esk3_0))|~r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_212]), c_0_183]), c_0_152])]), c_0_184]), c_0_130])).
% 50.22/50.47  cnf(c_0_239, negated_conjecture, (k2_tsep_1(esk3_0,X1,esk3_0)=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_136]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_240, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_36]), c_0_21]), c_0_23])]), c_0_24]), c_0_50])).
% 50.22/50.47  cnf(c_0_241, negated_conjecture, (r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_123]), c_0_124]), c_0_124]), c_0_124]), c_0_104]), c_0_63])]), c_0_127]), c_0_48])).
% 50.22/50.47  cnf(c_0_242, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)|~r1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214, c_0_192]), c_0_20]), c_0_38])]), c_0_127]), c_0_48]), c_0_25])).
% 50.22/50.47  cnf(c_0_243, negated_conjecture, (k2_tsep_1(esk1_0,esk3_0,esk4_0)=k2_tsep_1(esk1_0,esk4_0,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215, c_0_216]), c_0_36])]), c_0_50])).
% 50.22/50.47  cnf(c_0_244, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_217]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_245, negated_conjecture, (v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_218]), c_0_219])]), c_0_130])).
% 50.22/50.47  cnf(c_0_246, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk3_0,X1,k2_tsep_1(esk1_0,esk2_0,esk3_0)))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_152]), c_0_46]), c_0_61])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_247, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_220, c_0_200]), c_0_130])).
% 50.22/50.47  cnf(c_0_248, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_221, c_0_200]), c_0_130])).
% 50.22/50.47  cnf(c_0_249, negated_conjecture, (~v2_struct_0(g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_222]), c_0_152]), c_0_46])]), c_0_130]), c_0_50])).
% 50.22/50.47  cnf(c_0_250, negated_conjecture, (r1_tsep_1(esk2_0,esk2_0)|m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_223]), c_0_38]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_251, negated_conjecture, (k2_tsep_1(esk2_0,X1,esk2_0)=k2_tsep_1(esk2_0,esk2_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_224]), c_0_48])).
% 50.22/50.47  cnf(c_0_252, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_225, c_0_207])]), c_0_178])).
% 50.22/50.47  cnf(c_0_253, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,X1,X2)),esk3_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_226]), c_0_36])]), c_0_50]), c_0_128])).
% 50.22/50.47  cnf(c_0_254, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),X3)|v2_struct_0(k2_tsep_1(esk1_0,X1,X2))|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X3,k2_tsep_1(esk1_0,X1,X2))|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_172]), c_0_128])).
% 50.22/50.47  cnf(c_0_255, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)=k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_227]), c_0_200]), c_0_38])]), c_0_130]), c_0_48]), c_0_228])).
% 50.22/50.47  cnf(c_0_256, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_229]), c_0_200])]), c_0_130])).
% 50.22/50.47  cnf(c_0_257, negated_conjecture, (~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_230, c_0_172]), c_0_129]), c_0_36]), c_0_38])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_258, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_123]), c_0_124]), c_0_124]), c_0_124]), c_0_104]), c_0_63])]), c_0_127]), c_0_48])).
% 50.22/50.47  cnf(c_0_259, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk3_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_231]), c_0_36])]), c_0_50]), c_0_232])).
% 50.22/50.47  cnf(c_0_260, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_233, c_0_175]), c_0_36]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_261, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))|~r1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_234, c_0_235]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_262, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236, c_0_152]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_263, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk3_0,esk3_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237, c_0_238]), c_0_183])]), c_0_184])).
% 50.22/50.47  cnf(c_0_264, negated_conjecture, (k2_tsep_1(esk3_0,esk3_0,esk3_0)=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_239]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_265, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_240, c_0_65]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_266, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_38]), c_0_21]), c_0_23])]), c_0_24]), c_0_48])).
% 50.22/50.47  cnf(c_0_267, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_200]), c_0_32]), c_0_36]), c_0_38])]), c_0_130]), c_0_50]), c_0_48]), c_0_24])).
% 50.22/50.47  cnf(c_0_268, negated_conjecture, (~r1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241, c_0_242]), c_0_36])]), c_0_79]), c_0_50])).
% 50.22/50.47  cnf(c_0_269, negated_conjecture, (k2_tsep_1(esk1_0,esk3_0,esk4_0)=k2_tsep_1(esk1_0,esk4_0,esk3_0)|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_155]), c_0_156]), c_0_156]), c_0_157]), c_0_156]), c_0_158]), c_0_60])]), c_0_159]), c_0_50])).
% 50.22/50.47  cnf(c_0_270, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk2_0)|~r1_tsep_1(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_192]), c_0_20]), c_0_38])]), c_0_127]), c_0_48]), c_0_25]), c_0_99])).
% 50.22/50.47  cnf(c_0_271, negated_conjecture, (~r1_tsep_1(esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245, c_0_246]), c_0_222]), c_0_222]), c_0_247]), c_0_222]), c_0_248]), c_0_152])]), c_0_249]), c_0_130])).
% 50.22/50.47  cnf(c_0_272, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),esk2_0)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_250]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_273, negated_conjecture, (k2_tsep_1(esk2_0,X1,esk2_0)=k2_tsep_1(esk2_0,esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251, c_0_63]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_274, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_252, c_0_253]), c_0_36]), c_0_38])]), c_0_50]), c_0_178]), c_0_48])).
% 50.22/50.47  cnf(c_0_275, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)=k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254, c_0_255]), c_0_38]), c_0_36])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_276, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[c_0_256, c_0_257])).
% 50.22/50.47  cnf(c_0_277, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk2_0)|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258, c_0_259]), c_0_260]), c_0_104])]), c_0_232]), c_0_127])).
% 50.22/50.47  cnf(c_0_278, negated_conjecture, (r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~r1_tsep_1(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_123]), c_0_124]), c_0_124]), c_0_124]), c_0_104]), c_0_63])]), c_0_127]), c_0_48])).
% 50.22/50.47  cnf(c_0_279, negated_conjecture, (r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~r1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_261, c_0_101]), c_0_38]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_280, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,esk3_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_262]), c_0_130])).
% 50.22/50.47  cnf(c_0_281, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_155]), c_0_156]), c_0_156]), c_0_156]), c_0_135]), c_0_60])]), c_0_159]), c_0_50])).
% 50.22/50.47  cnf(c_0_282, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_263, c_0_264])).
% 50.22/50.47  cnf(c_0_283, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237, c_0_265]), c_0_60]), c_0_200])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_284, negated_conjecture, (r1_tsep_1(X1,esk1_0)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk1_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_32]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_285, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~r1_tsep_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266, c_0_38]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_286, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_219]), c_0_36]), c_0_38])]), c_0_50]), c_0_48]), c_0_200])]), c_0_130])).
% 50.22/50.47  cnf(c_0_287, negated_conjecture, (k2_tsep_1(esk1_0,X1,esk1_0)=k2_tsep_1(esk1_0,esk1_0,X1)|r1_tsep_1(X1,esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_32]), c_0_24])).
% 50.22/50.47  cnf(c_0_288, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,esk1_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_267]), c_0_130])).
% 50.22/50.47  cnf(c_0_289, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk2_0))|v2_struct_0(X1)|~r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_197]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_290, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_291, negated_conjecture, (k2_tsep_1(esk1_0,esk3_0,esk4_0)=k2_tsep_1(esk1_0,esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268, c_0_92]), c_0_20])]), c_0_25]), c_0_269])).
% 50.22/50.47  cnf(c_0_292, negated_conjecture, (k2_tsep_1(esk1_0,esk2_0,esk4_0)=k2_tsep_1(esk1_0,esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_216]), c_0_20]), c_0_38])]), c_0_25]), c_0_48])).
% 50.22/50.47  cnf(c_0_293, negated_conjecture, (~r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241, c_0_270]), c_0_38])]), c_0_271]), c_0_48])).
% 50.22/50.47  cnf(c_0_294, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_272, c_0_123]), c_0_124]), c_0_124]), c_0_125]), c_0_124]), c_0_126]), c_0_63])]), c_0_127]), c_0_48])).
% 50.22/50.47  cnf(c_0_295, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk2_0,X1,X2),esk2_0)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_49]), c_0_48])).
% 50.22/50.47  cnf(c_0_296, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k2_tsep_1(esk2_0,X1,esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_273]), c_0_63]), c_0_49])]), c_0_48])).
% 50.22/50.47  cnf(c_0_297, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254, c_0_274]), c_0_36]), c_0_38])]), c_0_178]), c_0_50]), c_0_48])).
% 50.22/50.47  cnf(c_0_298, negated_conjecture, (k2_tsep_1(esk1_0,esk3_0,k2_tsep_1(esk1_0,esk2_0,esk2_0))=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_275, c_0_257]), c_0_276])).
% 50.22/50.47  cnf(c_0_299, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0)|~r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277, c_0_101]), c_0_36]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_300, negated_conjecture, (~r1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_279]), c_0_36])]), c_0_79]), c_0_50])).
% 50.22/50.47  cnf(c_0_301, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_265]), c_0_38])]), c_0_48])).
% 50.22/50.47  fof(c_0_302, plain, ![X44, X45, X46, X47]:((~m1_pre_topc(X45,X47)|m1_pre_topc(k2_tsep_1(X44,X45,X46),k2_tsep_1(X44,X47,X46))|r1_tsep_1(X45,X46)|(v2_struct_0(X47)|~m1_pre_topc(X47,X44))|(v2_struct_0(X46)|~m1_pre_topc(X46,X44))|(v2_struct_0(X45)|~m1_pre_topc(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(~m1_pre_topc(X46,X47)|m1_pre_topc(k2_tsep_1(X44,X45,X46),k2_tsep_1(X44,X45,X47))|r1_tsep_1(X45,X46)|(v2_struct_0(X47)|~m1_pre_topc(X47,X44))|(v2_struct_0(X46)|~m1_pre_topc(X46,X44))|(v2_struct_0(X45)|~m1_pre_topc(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_tmap_1])])])])])).
% 50.22/50.47  cnf(c_0_303, negated_conjecture, (v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_280, c_0_152]), c_0_46]), c_0_61])]), c_0_50])).
% 50.22/50.47  cnf(c_0_304, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)|~r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_281, c_0_282]), c_0_200])]), c_0_130])).
% 50.22/50.47  cnf(c_0_305, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283, c_0_198]), c_0_20]), c_0_36]), c_0_38])]), c_0_79]), c_0_48]), c_0_50]), c_0_25])).
% 50.22/50.47  cnf(c_0_306, negated_conjecture, (r1_tsep_1(X1,esk1_0)|v2_struct_0(X1)|~r1_tsep_1(esk1_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_32]), c_0_32])]), c_0_24])).
% 50.22/50.47  cnf(c_0_307, negated_conjecture, (~r1_tsep_1(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_285]), c_0_38]), c_0_36])]), c_0_79]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_308, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)=k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286, c_0_287]), c_0_32]), c_0_200])]), c_0_24]), c_0_130])).
% 50.22/50.47  cnf(c_0_309, negated_conjecture, (v2_struct_0(X1)|~r1_tsep_1(X1,esk1_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_288, c_0_128]), c_0_21]), c_0_23]), c_0_36]), c_0_38])]), c_0_24]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_310, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)|v2_struct_0(X1)|~r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_289, c_0_207])]), c_0_178])).
% 50.22/50.47  cnf(c_0_311, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_290, c_0_291])])).
% 50.22/50.47  cnf(c_0_312, negated_conjecture, (k2_tsep_1(esk1_0,esk2_0,esk4_0)=k2_tsep_1(esk1_0,esk4_0,esk2_0)), inference(sr,[status(thm)],[c_0_292, c_0_293])).
% 50.22/50.47  cnf(c_0_313, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_129]), c_0_49]), c_0_103])]), c_0_48]), c_0_130])).
% 50.22/50.47  cnf(c_0_314, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk2_0,esk2_0,esk2_0),X1)|v2_struct_0(k2_tsep_1(esk2_0,esk2_0,esk2_0))|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,esk2_0),X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X2,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_294]), c_0_49]), c_0_103])]), c_0_48])).
% 50.22/50.47  cnf(c_0_315, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk2_0,esk2_0,X1),esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_295, c_0_273]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_316, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk2_0,esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_296, c_0_273]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_317, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk3_0)), inference(rw,[status(thm)],[c_0_297, c_0_298])).
% 50.22/50.47  cnf(c_0_318, negated_conjecture, (~r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_299]), c_0_38])]), c_0_300]), c_0_48])).
% 50.22/50.47  cnf(c_0_319, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 50.22/50.47  cnf(c_0_320, negated_conjecture, (k2_tsep_1(esk1_0,esk2_0,esk4_0)=k2_tsep_1(esk1_0,esk4_0,esk2_0)|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301, c_0_216]), c_0_38])]), c_0_48])).
% 50.22/50.47  cnf(c_0_321, plain, (m1_pre_topc(k2_tsep_1(X3,X4,X1),k2_tsep_1(X3,X4,X2))|r1_tsep_1(X4,X1)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_302])).
% 50.22/50.47  cnf(c_0_322, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)=k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283, c_0_216]), c_0_200])]), c_0_130])).
% 50.22/50.47  cnf(c_0_323, negated_conjecture, (~r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_303, c_0_304]), c_0_219]), c_0_152])]), c_0_130])).
% 50.22/50.47  cnf(c_0_324, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))|r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_305, c_0_291])).
% 50.22/50.47  cnf(c_0_325, negated_conjecture, (k2_tsep_1(esk1_0,esk3_0,esk1_0)=k2_tsep_1(esk1_0,esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_306, c_0_92]), c_0_36]), c_0_32])]), c_0_307]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_326, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)=k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_306, c_0_308]), c_0_200])]), c_0_130])).
% 50.22/50.47  cnf(c_0_327, negated_conjecture, (~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_309, c_0_172]), c_0_200]), c_0_36]), c_0_38])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_328, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),X1)|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_310, c_0_176]), c_0_178])).
% 50.22/50.47  cnf(c_0_329, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_311, c_0_312])])).
% 50.22/50.47  cnf(c_0_330, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_291]), c_0_20]), c_0_36])]), c_0_50]), c_0_25])).
% 50.22/50.47  cnf(c_0_331, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_291]), c_0_20]), c_0_36]), c_0_21])]), c_0_25]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_332, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~r1_tsep_1(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266, c_0_123]), c_0_124]), c_0_124]), c_0_124]), c_0_104]), c_0_63])]), c_0_127]), c_0_48])).
% 50.22/50.47  cnf(c_0_333, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk3_0),X1)|v2_struct_0(X1)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_231]), c_0_36])]), c_0_50]), c_0_232])).
% 50.22/50.47  cnf(c_0_334, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|v2_struct_0(X1)|~r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_172]), c_0_129]), c_0_36]), c_0_38])]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_335, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk2_0,esk2_0,esk2_0),X1)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_314, c_0_315]), c_0_63])]), c_0_316]), c_0_48])).
% 50.22/50.47  cnf(c_0_336, negated_conjecture, (k2_tsep_1(esk2_0,X1,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_103]), c_0_49])]), c_0_48])).
% 50.22/50.47  cnf(c_0_337, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_317, c_0_101]), c_0_38]), c_0_63])]), c_0_318]), c_0_48])).
% 50.22/50.47  cnf(c_0_338, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_276]), c_0_38]), c_0_200]), c_0_21])]), c_0_48]), c_0_130]), c_0_24])).
% 50.22/50.47  cnf(c_0_339, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_319, c_0_320])).
% 50.22/50.47  cnf(c_0_340, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0)|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_320]), c_0_20]), c_0_38])]), c_0_48]), c_0_25])).
% 50.22/50.47  cnf(c_0_341, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)|~v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_320]), c_0_20]), c_0_38]), c_0_21])]), c_0_25]), c_0_48]), c_0_24])).
% 50.22/50.47  cnf(c_0_342, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),k2_tsep_1(esk1_0,X1,X3))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  cnf(c_0_343, plain, (m1_pre_topc(k2_tsep_1(X3,X1,X4),k2_tsep_1(X3,X2,X4))|r1_tsep_1(X1,X4)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_302])).
% 50.22/50.47  cnf(c_0_344, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)=k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[c_0_322, c_0_323])).
% 50.22/50.47  cnf(c_0_345, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)=k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[c_0_324, c_0_323])).
% 50.22/50.47  cnf(c_0_346, negated_conjecture, (k2_tsep_1(esk1_0,esk1_0,esk3_0)=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_325]), c_0_32]), c_0_36])]), c_0_50]), c_0_24])).
% 50.22/50.47  cnf(c_0_347, negated_conjecture, (k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)=k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[c_0_326, c_0_327])).
% 50.22/50.47  cnf(c_0_348, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk2_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_328, c_0_329]), c_0_330])]), c_0_331])).
% 50.22/50.47  cnf(c_0_349, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk3_0),esk2_0)|~r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_332, c_0_333]), c_0_260]), c_0_104])]), c_0_232]), c_0_127])).
% 50.22/50.47  cnf(c_0_350, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk2_0,esk2_0,esk2_0))|~r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_334, c_0_335]), c_0_294]), c_0_129])]), c_0_316]), c_0_130])).
% 50.22/50.47  cnf(c_0_351, negated_conjecture, (k2_tsep_1(esk2_0,X1,esk2_0)=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_336, c_0_273]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_352, negated_conjecture, (r1_tsep_1(X1,esk4_0)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_20]), c_0_21]), c_0_23])]), c_0_24]), c_0_25])).
% 50.22/50.47  cnf(c_0_353, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)))|v2_struct_0(X1)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_337]), c_0_36]), c_0_200]), c_0_38])]), c_0_338]), c_0_130]), c_0_48]), c_0_50])).
% 50.22/50.47  cnf(c_0_354, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk4_0,esk2_0))|m1_pre_topc(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_339]), c_0_340]), c_0_341])).
% 50.22/50.47  cnf(c_0_355, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_312]), c_0_20]), c_0_38])]), c_0_48]), c_0_25])).
% 50.22/50.47  cnf(c_0_356, negated_conjecture, (~v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_312]), c_0_20]), c_0_38]), c_0_21])]), c_0_25]), c_0_48]), c_0_24])).
% 50.22/50.47  cnf(c_0_357, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X2)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),k2_tsep_1(esk1_0,esk3_0,X2))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_342, c_0_36]), c_0_50])).
% 50.22/50.47  cnf(c_0_358, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),k2_tsep_1(esk1_0,X3,X2))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_343, c_0_23]), c_0_21])]), c_0_24])).
% 50.22/50.47  cnf(c_0_359, negated_conjecture, (k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))=k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_344, c_0_345])).
% 50.22/50.47  cnf(c_0_360, negated_conjecture, (k2_tsep_1(esk1_0,esk4_0,esk3_0)=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_269]), c_0_20]), c_0_36])]), c_0_50]), c_0_25]), c_0_65])).
% 50.22/50.47  cnf(c_0_361, negated_conjecture, (k2_tsep_1(esk1_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_327, c_0_198]), c_0_325]), c_0_346]), c_0_32]), c_0_36]), c_0_38])]), c_0_79]), c_0_48]), c_0_50]), c_0_24]), c_0_347])).
% 50.22/50.47  cnf(c_0_362, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk4_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_348, c_0_101]), c_0_38]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_363, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0)|~r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_349, c_0_101]), c_0_36]), c_0_60])]), c_0_50])).
% 50.22/50.47  cnf(c_0_364, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk2_0,esk2_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_350]), c_0_294])]), c_0_316])).
% 50.22/50.47  cnf(c_0_365, negated_conjecture, (k2_tsep_1(esk2_0,esk2_0,esk2_0)=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273, c_0_351]), c_0_63])]), c_0_48])).
% 50.22/50.47  cnf(c_0_366, negated_conjecture, (r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_352, c_0_30]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_367, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_353, c_0_354]), c_0_355])]), c_0_356])).
% 50.22/50.47  cnf(c_0_368, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),k2_tsep_1(esk1_0,esk4_0,esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_357, c_0_20]), c_0_25]), c_0_291])).
% 50.22/50.47  cnf(c_0_369, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X2)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),k2_tsep_1(esk1_0,X2,esk2_0))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_358, c_0_38]), c_0_48])).
% 50.22/50.47  cnf(c_0_370, negated_conjecture, (k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))=k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359, c_0_360]), c_0_361])).
% 50.22/50.47  cnf(c_0_371, negated_conjecture, (k2_tsep_1(esk1_0,esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))=g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_347]), c_0_32]), c_0_200])]), c_0_130]), c_0_24])).
% 50.22/50.47  cnf(c_0_372, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_78]), c_0_60]), c_0_200])]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_373, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk4_0,esk3_0))|r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk4_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_362]), c_0_355])]), c_0_356])).
% 50.22/50.47  cnf(c_0_374, negated_conjecture, (~r1_tsep_1(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_363]), c_0_38])]), c_0_300]), c_0_48])).
% 50.22/50.47  cnf(c_0_375, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_364, c_0_365])).
% 50.22/50.47  cnf(c_0_376, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,k2_tsep_1(esk1_0,esk2_0,esk3_0)),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_200]), c_0_130])).
% 50.22/50.47  cnf(c_0_377, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_366, c_0_88]), c_0_38]), c_0_20])]), c_0_48]), c_0_25])).
% 50.22/50.47  cnf(c_0_378, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0)|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_88]), c_0_20])]), c_0_25])).
% 50.22/50.47  cnf(c_0_379, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),k2_tsep_1(esk1_0,esk4_0,esk2_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254, c_0_367]), c_0_355]), c_0_200]), c_0_38])]), c_0_338]), c_0_356]), c_0_48]), c_0_130])).
% 50.22/50.47  cnf(c_0_380, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X1,X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_108]), c_0_38]), c_0_36])]), c_0_48]), c_0_50]), c_0_130])).
% 50.22/50.47  cnf(c_0_381, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))|~m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_368]), c_0_108]), c_0_36]), c_0_38])]), c_0_79]), c_0_50]), c_0_48])).
% 50.22/50.47  cnf(c_0_382, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_369, c_0_20]), c_0_25])).
% 50.22/50.47  cnf(c_0_383, plain, (m1_pre_topc(X3,X2)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|k2_tsep_1(X1,X2,X3)!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 50.22/50.47  cnf(c_0_384, negated_conjecture, (k2_tsep_1(esk1_0,esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))=g1_pre_topc(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)))|m1_pre_topc(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_370, c_0_371])).
% 50.22/50.47  cnf(c_0_385, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_303, c_0_372]), c_0_219]), c_0_152])]), c_0_130])).
% 50.22/50.47  cnf(c_0_386, negated_conjecture, (r1_tsep_1(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),k2_tsep_1(esk1_0,esk4_0,esk3_0))|~m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_373, c_0_101]), c_0_20]), c_0_38])]), c_0_374]), c_0_48]), c_0_25])).
% 50.22/50.47  cnf(c_0_387, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)|~r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258, c_0_375]), c_0_200])]), c_0_130])).
% 50.22/50.47  cnf(c_0_388, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)|m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_376]), c_0_200]), c_0_38])]), c_0_130]), c_0_48])).
% 50.22/50.47  cnf(c_0_389, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_377]), c_0_25]), c_0_48]), c_0_378])).
% 50.22/50.47  cnf(c_0_390, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),k2_tsep_1(esk1_0,esk4_0,esk2_0))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_379]), c_0_356]), c_0_338])).
% 50.22/50.47  cnf(c_0_391, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,k2_tsep_1(esk1_0,esk4_0,esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_380, c_0_381]), c_0_330])]), c_0_331])).
% 50.22/50.47  cnf(c_0_392, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),k2_tsep_1(esk1_0,esk4_0,esk2_0))|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257, c_0_382]), c_0_200])]), c_0_130]), c_0_276])).
% 50.22/50.47  cnf(c_0_393, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|m1_pre_topc(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_383, c_0_384]), c_0_200]), c_0_20]), c_0_21]), c_0_23])]), c_0_130]), c_0_25]), c_0_24]), c_0_385])).
% 50.22/50.47  cnf(c_0_394, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk4_0,esk3_0))|~m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241, c_0_386]), c_0_330])]), c_0_331])).
% 50.22/50.47  cnf(c_0_395, negated_conjecture, (~r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_257, c_0_387])).
% 50.22/50.47  cnf(c_0_396, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)),esk2_0)), inference(sr,[status(thm)],[c_0_388, c_0_257])).
% 50.22/50.47  cnf(c_0_397, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_389, c_0_38]), c_0_20]), c_0_21]), c_0_23])]), c_0_24])).
% 50.22/50.47  cnf(c_0_398, plain, ($false), inference(cdclpropres,[status(thm)],[c_0_390, c_0_391, c_0_392, c_0_393, c_0_394, c_0_395, c_0_48, c_0_396, c_0_397, c_0_103, c_0_49, c_0_38]), ['proof']).
% 50.22/50.47  # SZS output end CNFRefutation
% 50.22/50.47  # Proof object total steps             : 399
% 50.22/50.47  # Proof object clause steps            : 370
% 50.22/50.47  # Proof object formula steps           : 29
% 50.22/50.47  # Proof object conjectures             : 346
% 50.22/50.47  # Proof object clause conjectures      : 343
% 50.22/50.47  # Proof object formula conjectures     : 3
% 50.22/50.47  # Proof object initial clauses used    : 37
% 50.22/50.47  # Proof object initial formulas used   : 14
% 50.22/50.47  # Proof object generating inferences   : 314
% 50.22/50.47  # Proof object simplifying inferences  : 1235
% 50.22/50.47  # Training examples: 0 positive, 0 negative
% 50.22/50.47  # Parsed axioms                        : 15
% 50.22/50.47  # Removed by relevancy pruning/SinE    : 0
% 50.22/50.47  # Initial clauses                      : 43
% 50.22/50.47  # Removed in clause preprocessing      : 0
% 50.22/50.47  # Initial clauses in saturation        : 43
% 50.22/50.47  # Processed clauses                    : 126910
% 50.22/50.47  # ...of these trivial                  : 2414
% 50.22/50.47  # ...subsumed                          : 104496
% 50.22/50.47  # ...remaining for further processing  : 20000
% 50.22/50.47  # Other redundant clauses eliminated   : 0
% 50.22/50.47  # Clauses deleted for lack of memory   : 289862
% 50.22/50.47  # Backward-subsumed                    : 2756
% 50.22/50.47  # Backward-rewritten                   : 2485
% 50.22/50.47  # Generated clauses                    : 2207570
% 50.22/50.47  # ...of the previous two non-trivial   : 2103450
% 50.22/50.47  # Contextual simplify-reflections      : 3104
% 50.22/50.47  # Paramodulations                      : 2207438
% 50.22/50.47  # Factorizations                       : 0
% 50.22/50.47  # Equation resolutions                 : 0
% 50.22/50.47  # Propositional unsat checks           : 4
% 50.22/50.47  #    Propositional check models        : 0
% 50.22/50.47  #    Propositional check unsatisfiable : 1
% 50.22/50.47  #    Propositional clauses             : 1096217
% 50.22/50.47  #    Propositional clauses after purity: 67427
% 50.22/50.47  #    Propositional unsat core size     : 12
% 50.22/50.47  #    Propositional preprocessing time  : 0.000
% 50.22/50.47  #    Propositional encoding time       : 3.318
% 50.22/50.47  #    Propositional solver time         : 1.173
% 50.22/50.47  #    Success case prop preproc time    : 0.000
% 50.22/50.47  #    Success case prop encoding time   : 1.083
% 50.22/50.47  #    Success case prop solver time     : 0.399
% 50.22/50.47  # Current number of processed clauses  : 14584
% 50.22/50.47  #    Positive orientable unit clauses  : 1008
% 50.22/50.47  #    Positive unorientable unit clauses: 0
% 50.22/50.47  #    Negative unit clauses             : 110
% 50.22/50.47  #    Non-unit-clauses                  : 13466
% 50.22/50.47  # Current number of unprocessed clauses: 1081633
% 50.22/50.47  # ...number of literals in the above   : 8174436
% 50.22/50.47  # Current number of archived formulas  : 0
% 50.22/50.47  # Current number of archived clauses   : 5416
% 50.22/50.47  # Clause-clause subsumption calls (NU) : 43405116
% 50.22/50.47  # Rec. Clause-clause subsumption calls : 5427134
% 50.22/50.47  # Non-unit clause-clause subsumptions  : 65009
% 50.22/50.47  # Unit Clause-clause subsumption calls : 497447
% 50.22/50.47  # Rewrite failures with RHS unbound    : 0
% 50.22/50.47  # BW rewrite match attempts            : 78744
% 50.22/50.47  # BW rewrite match successes           : 359
% 50.22/50.47  # Condensation attempts                : 0
% 50.22/50.47  # Condensation successes               : 0
% 50.22/50.47  # Termbank termtop insertions          : 141381437
% 50.32/50.55  
% 50.32/50.55  # -------------------------------------------------
% 50.32/50.55  # User time                : 49.040 s
% 50.32/50.55  # System time              : 1.147 s
% 50.32/50.55  # Total time               : 50.187 s
% 50.32/50.55  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
