%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1736+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:40 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 919 expanded)
%              Number of clauses        :   64 ( 288 expanded)
%              Number of leaves         :   11 ( 222 expanded)
%              Depth                    :   16
%              Number of atoms          :  597 (10429 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_tmap_1,conjecture,(
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
                    & v1_borsuk_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ( ( m1_pre_topc(X2,X4)
                      & r1_tsep_1(X4,X3) )
                   => ( v1_borsuk_1(X2,k1_tsep_1(X1,X2,X3))
                      & m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
                      & v1_borsuk_1(X2,k1_tsep_1(X1,X3,X2))
                      & m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tmap_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

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

fof(t43_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X3,X2)
               => ( v1_borsuk_1(k2_tsep_1(X1,X3,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X3,X2),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tmap_1)).

fof(t33_tmap_1,axiom,(
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
                   => ( ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) )
                      | ( k2_tsep_1(X1,X3,k1_tsep_1(X1,X2,X4)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & k2_tsep_1(X1,X3,k1_tsep_1(X1,X4,X2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t13_tmap_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_borsuk_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

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

fof(c_0_11,negated_conjecture,(
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
                      & v1_borsuk_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ( ( m1_pre_topc(X2,X4)
                        & r1_tsep_1(X4,X3) )
                     => ( v1_borsuk_1(X2,k1_tsep_1(X1,X2,X3))
                        & m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
                        & v1_borsuk_1(X2,k1_tsep_1(X1,X3,X2))
                        & m1_pre_topc(X2,k1_tsep_1(X1,X3,X2)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_tmap_1])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( v2_struct_0(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,X7)
      | k1_tsep_1(X7,X8,X9) = k1_tsep_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & v1_borsuk_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk4_0)
    & r1_tsep_1(esk4_0,esk3_0)
    & ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
      | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X24)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X24)
      | m1_pre_topc(X25,k1_tsep_1(X24,X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

fof(c_0_15,plain,(
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

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r1_tsep_1(X29,X30)
        | r1_tsep_1(X28,X30)
        | ~ m1_pre_topc(X28,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tsep_1(X30,X29)
        | r1_tsep_1(X28,X30)
        | ~ m1_pre_topc(X28,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tsep_1(X29,X30)
        | r1_tsep_1(X30,X28)
        | ~ m1_pre_topc(X28,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tsep_1(X30,X29)
        | r1_tsep_1(X30,X28)
        | ~ m1_pre_topc(X28,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_23])]),c_0_19]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_33,plain,(
    ! [X35,X36,X37] :
      ( ( v1_borsuk_1(k2_tsep_1(X35,X37,X36),X36)
        | r1_tsep_1(X37,X36)
        | v2_struct_0(X37)
        | ~ v1_borsuk_1(X37,X35)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_pre_topc(k2_tsep_1(X35,X37,X36),X36)
        | r1_tsep_1(X37,X36)
        | v2_struct_0(X37)
        | ~ v1_borsuk_1(X37,X35)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_tmap_1])])])])])).

fof(c_0_34,plain,(
    ! [X31,X32,X33,X34] :
      ( ( k2_tsep_1(X31,X33,k1_tsep_1(X31,X32,X34)) = g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ r1_tsep_1(X33,X34)
        | ~ m1_pre_topc(X32,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( k2_tsep_1(X31,X33,k1_tsep_1(X31,X34,X32)) = g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ r1_tsep_1(X33,X34)
        | ~ m1_pre_topc(X32,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( k2_tsep_1(X31,X33,k1_tsep_1(X31,X32,X34)) = g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ r1_tsep_1(X34,X33)
        | ~ m1_pre_topc(X32,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( k2_tsep_1(X31,X33,k1_tsep_1(X31,X34,X32)) = g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ r1_tsep_1(X34,X33)
        | ~ m1_pre_topc(X32,X33)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_tmap_1])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_18]),c_0_23])]),c_0_20]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26]),c_0_17]),c_0_18])]),c_0_27]),c_0_19]),c_0_20])).

cnf(c_0_39,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( k2_tsep_1(X1,X2,k1_tsep_1(X1,X3,X4)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_45,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,X1),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_18]),c_0_23])]),c_0_42]),c_0_20])).

fof(c_0_48,plain,(
    ! [X18,X19,X20] :
      ( ( v1_borsuk_1(X20,X18)
        | ~ v1_borsuk_1(X19,X18)
        | ~ m1_pre_topc(X19,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_pre_topc(X20,X18)
        | ~ v1_borsuk_1(X19,X18)
        | ~ m1_pre_topc(X19,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v1_borsuk_1(X19,X18)
        | ~ v1_borsuk_1(X20,X18)
        | ~ m1_pre_topc(X20,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_pre_topc(X19,X18)
        | ~ v1_borsuk_1(X20,X18)
        | ~ m1_pre_topc(X20,X18)
        | X20 != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_tmap_1])])])])).

fof(c_0_49,plain,(
    ! [X5,X6] :
      ( ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_50,negated_conjecture,
    ( k2_tsep_1(X1,esk4_0,k1_tsep_1(X1,X2,esk3_0)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_19]),c_0_42])).

cnf(c_0_51,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_tsep_1(X22,X23)
        | ~ m1_pre_topc(X22,X23)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_tsep_1(X23,X22)
        | ~ m1_pre_topc(X22,X23)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_41]),c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_38])).

cnf(c_0_55,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v1_borsuk_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_17]),c_0_41]),c_0_18]),c_0_23])]),c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_18])])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_64,plain,
    ( v1_borsuk_1(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_65,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_55,c_0_56]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26])]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_58]),c_0_59])])).

cnf(c_0_68,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_26]),c_0_18]),c_0_23])])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58])]),c_0_27]),c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_36])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_26]),c_0_18]),c_0_23])]),c_0_20]),c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( v1_borsuk_1(k2_tsep_1(esk1_0,X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_borsuk_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_37]),c_0_18]),c_0_23])]),c_0_20]),c_0_38])).

cnf(c_0_73,negated_conjecture,
    ( v1_borsuk_1(esk2_0,X1)
    | ~ v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_41]),c_0_18]),c_0_23])]),c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_18]),c_0_23])])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_borsuk_1(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_32]),c_0_32]),c_0_36])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_41]),c_0_40])]),c_0_42])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_borsuk_1(k2_tsep_1(esk1_0,esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)),k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])]),c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_41]),c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,plain,
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

cnf(c_0_84,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_58])]),c_0_42]),c_0_27])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_41]),c_0_26]),c_0_18]),c_0_23])]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
