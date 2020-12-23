%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t34_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:13 EDT 2019

% Result     : Theorem 167.65s
% Output     : CNFRefutation 167.65s
% Verified   : 
% Statistics : Number of formulae       :  127 (25443 expanded)
%              Number of clauses        :  112 (7915 expanded)
%              Number of leaves         :    7 (6075 expanded)
%              Depth                    :   30
%              Number of atoms          :  729 (337423 expanded)
%              Number of equality atoms :   16 (1891 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',t34_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',t29_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',dt_k2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',t32_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',t23_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',t30_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t34_tmap_1.p',t22_tmap_1)).

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
    ! [X42,X43,X44,X45] :
      ( ( r1_tsep_1(X43,X44)
        | k2_tsep_1(X42,X43,X44) = k2_tsep_1(X42,X44,X43)
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X42)
        | v2_struct_0(X44)
        | ~ m1_pre_topc(X44,X42)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( r1_tsep_1(X43,X44)
        | r1_tsep_1(k2_tsep_1(X42,X43,X44),X45)
        | k2_tsep_1(X42,k2_tsep_1(X42,X43,X44),X45) = k2_tsep_1(X42,X43,k2_tsep_1(X42,X44,X45))
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X42)
        | v2_struct_0(X44)
        | ~ m1_pre_topc(X44,X42)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( r1_tsep_1(X44,X45)
        | r1_tsep_1(X43,k2_tsep_1(X42,X44,X45))
        | k2_tsep_1(X42,k2_tsep_1(X42,X43,X44),X45) = k2_tsep_1(X42,X43,k2_tsep_1(X42,X44,X45))
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X42)
        | v2_struct_0(X44)
        | ~ m1_pre_topc(X44,X42)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_tsep_1])])])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v2_struct_0(k2_tsep_1(X14,X15,X16))
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X14) )
      & ( v1_pre_topc(k2_tsep_1(X14,X15,X16))
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X14) )
      & ( m1_pre_topc(k2_tsep_1(X14,X15,X16),X14)
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_17,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,X2) = k2_tsep_1(esk1_0,X2,X1)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk3_0) = k2_tsep_1(esk1_0,esk3_0,X1)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_25,plain,(
    ! [X51,X52,X53,X54] :
      ( ( ~ m1_pre_topc(X52,X54)
        | m1_pre_topc(k2_tsep_1(X51,X52,X53),k2_tsep_1(X51,X54,X53))
        | r1_tsep_1(X52,X53)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X51)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X51)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ m1_pre_topc(X53,X54)
        | m1_pre_topc(k2_tsep_1(X51,X52,X53),k2_tsep_1(X51,X52,X54))
        | r1_tsep_1(X52,X53)
        | v2_struct_0(X54)
        | ~ m1_pre_topc(X54,X51)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X51)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_tmap_1])])])])])).

fof(c_0_26,plain,(
    ! [X38,X39,X40,X41] :
      ( ( ~ r1_tsep_1(X40,X41)
        | r1_tsep_1(X39,X41)
        | ~ m1_pre_topc(X39,X40)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r1_tsep_1(X41,X40)
        | r1_tsep_1(X39,X41)
        | ~ m1_pre_topc(X39,X40)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r1_tsep_1(X40,X41)
        | r1_tsep_1(X41,X39)
        | ~ m1_pre_topc(X39,X40)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r1_tsep_1(X41,X40)
        | r1_tsep_1(X41,X39)
        | ~ m1_pre_topc(X39,X40)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_12])]),c_0_19]),c_0_15])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk2_0) = k2_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22]),c_0_18]),c_0_12])]),c_0_24]),c_0_19]),c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,X1),k2_tsep_1(esk1_0,esk2_0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_12]),c_0_13])]),c_0_24]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_12]),c_0_13])]),c_0_15]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_22]),c_0_12])]),c_0_24]),c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk4_0) = k2_tsep_1(esk1_0,esk4_0,X1)
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11]),c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,X1),k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_11]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_23]),c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_45,plain,(
    ! [X48,X49,X50] :
      ( ( m1_pre_topc(k2_tsep_1(X48,X49,X50),X49)
        | r1_tsep_1(X49,X50)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( m1_pre_topc(k2_tsep_1(X48,X49,X50),X50)
        | r1_tsep_1(X49,X50)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_42]),c_0_11]),c_0_22]),c_0_12])]),c_0_14]),c_0_24]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
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

fof(c_0_51,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_tsep_1(X36,X37)
        | ~ m1_pre_topc(X36,X37)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r1_tsep_1(X37,X36)
        | ~ m1_pre_topc(X36,X37)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_12]),c_0_13])]),c_0_19]),c_0_15])).

cnf(c_0_55,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_32]),c_0_12]),c_0_13])]),c_0_15]),c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),k2_tsep_1(esk1_0,X2,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_18]),c_0_12]),c_0_13])]),c_0_19]),c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_18]),c_0_12]),c_0_13])]),c_0_15]),c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_33]),c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_68,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_11]),c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_11]),c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(esk2_0,esk4_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_44]),c_0_11])]),c_0_14])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_18]),c_0_32]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_72,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_68]),c_0_11]),c_0_18]),c_0_12])]),c_0_14]),c_0_19]),c_0_15])).

cnf(c_0_75,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_77,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_12]),c_0_13])]),c_0_15]),c_0_24])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_76]),c_0_11])]),c_0_14])).

cnf(c_0_81,plain,
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

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_18]),c_0_23]),c_0_19])).

cnf(c_0_84,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_18]),c_0_12]),c_0_13])]),c_0_19]),c_0_15])).

cnf(c_0_85,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_86,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])]),c_0_24]),c_0_33])).

cnf(c_0_89,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_12]),c_0_13])]),c_0_15]),c_0_19])).

cnf(c_0_90,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_22]),c_0_32]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_91,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,esk2_0) = k2_tsep_1(esk1_0,esk2_0,X1)
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_22]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_11])]),c_0_14])).

cnf(c_0_93,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_12])]),c_0_14]),c_0_15])).

cnf(c_0_94,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_11]),c_0_14])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_96,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_97,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk3_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19])).

cnf(c_0_98,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_99,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_22]),c_0_24])).

cnf(c_0_100,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk4_0) = k2_tsep_1(esk1_0,esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_22]),c_0_12]),c_0_13])]),c_0_24]),c_0_15])).

cnf(c_0_102,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_22]),c_0_12]),c_0_13])]),c_0_15]),c_0_24])).

cnf(c_0_104,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_105,negated_conjecture,
    ( ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_100]),c_0_11]),c_0_22]),c_0_12])]),c_0_14]),c_0_24]),c_0_15])).

cnf(c_0_106,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_11]),c_0_14])).

cnf(c_0_107,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_94])).

cnf(c_0_108,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ v2_struct_0(k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_97]),c_0_11]),c_0_18]),c_0_12])]),c_0_14]),c_0_19]),c_0_15])).

cnf(c_0_109,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_76]),c_0_11])]),c_0_14])).

cnf(c_0_110,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_12]),c_0_13])]),c_0_15]),c_0_33])).

cnf(c_0_111,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_100]),c_0_100]),c_0_100]),c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_106,c_0_95])).

cnf(c_0_113,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_107]),c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_18]),c_0_23]),c_0_19])).

cnf(c_0_115,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_18]),c_0_60])]),c_0_19])).

cnf(c_0_116,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_22]),c_0_112])]),c_0_24])).

cnf(c_0_117,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_79])]),c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_99])).

cnf(c_0_119,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_32]),c_0_33])).

cnf(c_0_120,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_117,c_0_95])).

cnf(c_0_121,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_100]),c_0_100]),c_0_100]),c_0_105])).

cnf(c_0_122,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_90])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_122,c_0_100])).

cnf(c_0_125,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_123]),c_0_124])]),c_0_33]),c_0_105])).

cnf(c_0_126,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_32]),c_0_40]),c_0_12]),c_0_13])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
