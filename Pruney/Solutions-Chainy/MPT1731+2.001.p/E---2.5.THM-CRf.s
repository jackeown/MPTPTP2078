%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:11 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   94 (2167 expanded)
%              Number of clauses        :   77 ( 795 expanded)
%              Number of leaves         :    8 ( 538 expanded)
%              Depth                    :   26
%              Number of atoms          :  550 (73276 expanded)
%              Number of equality atoms :   11 ( 110 expanded)
%              Maximal formula depth    :   51 (   5 average)
%              Maximal clause size      :  189 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_tmap_1,conjecture,(
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
                 => ( ( r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)
                     => ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X3,X4) ) )
                    & ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X3,X4) )
                     => r1_tsep_1(k1_tsep_1(X1,X2,X3),X4) )
                    & ( r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))
                     => ( r1_tsep_1(X4,X2)
                        & r1_tsep_1(X4,X3) ) )
                    & ( ( r1_tsep_1(X4,X2)
                        & r1_tsep_1(X4,X3) )
                     => r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d2_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_pre_topc(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X4 = k1_tsep_1(X1,X2,X3)
                  <=> u1_struct_0(X4) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_8,negated_conjecture,(
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
                   => ( ( r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)
                       => ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X3,X4) ) )
                      & ( ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X3,X4) )
                       => r1_tsep_1(k1_tsep_1(X1,X2,X3),X4) )
                      & ( r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))
                       => ( r1_tsep_1(X4,X2)
                          & r1_tsep_1(X4,X3) ) )
                      & ( ( r1_tsep_1(X4,X2)
                          & r1_tsep_1(X4,X3) )
                       => r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_tmap_1])).

fof(c_0_9,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_struct_0(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( v1_pre_topc(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(esk4_0,esk2_0)
      | ~ r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
      | ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ~ l1_struct_0(X20)
      | ~ l1_struct_0(X21)
      | ~ r1_tsep_1(X20,X21)
      | r1_tsep_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_13,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_21,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X11,X12,X13,X14] :
      ( ( X14 != k1_tsep_1(X11,X12,X13)
        | u1_struct_0(X14) = k2_xboole_0(u1_struct_0(X12),u1_struct_0(X13))
        | v2_struct_0(X14)
        | ~ v1_pre_topc(X14)
        | ~ m1_pre_topc(X14,X11)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) )
      & ( u1_struct_0(X14) != k2_xboole_0(u1_struct_0(X12),u1_struct_0(X13))
        | X14 = k1_tsep_1(X11,X12,X13)
        | v2_struct_0(X14)
        | ~ v1_pre_topc(X14)
        | ~ m1_pre_topc(X14,X11)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( u1_struct_0(X1) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k1_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_35,plain,(
    ! [X15,X16] :
      ( ( ~ r1_tsep_1(X15,X16)
        | r1_xboole_0(u1_struct_0(X15),u1_struct_0(X16))
        | ~ l1_struct_0(X16)
        | ~ l1_struct_0(X15) )
      & ( ~ r1_xboole_0(u1_struct_0(X15),u1_struct_0(X16))
        | r1_tsep_1(X15,X16)
        | ~ l1_struct_0(X16)
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_30]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_39,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_13]),c_0_33]),c_0_34])).

cnf(c_0_40,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_29])])).

fof(c_0_43,plain,(
    ! [X5,X6,X7] :
      ( ( r1_xboole_0(X5,k2_xboole_0(X6,X7))
        | ~ r1_xboole_0(X5,X6)
        | ~ r1_xboole_0(X5,X7) )
      & ( r1_xboole_0(X5,X6)
        | ~ r1_xboole_0(X5,k2_xboole_0(X6,X7)) )
      & ( r1_xboole_0(X5,X7)
        | ~ r1_xboole_0(X5,k2_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_14]),c_0_15])]),c_0_17]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_37])])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_29])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk3_0))
    | ~ r1_xboole_0(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_28]),c_0_37])])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_29])])).

cnf(c_0_55,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk2_0))
    | ~ r1_xboole_0(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_37])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_28]),c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_15])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_29])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_28]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_28]),c_0_29])])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_28]),c_0_60])])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_68])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_28]),c_0_29])])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_28]),c_0_64])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_28]),c_0_64])])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),k2_xboole_0(X1,u1_struct_0(esk3_0)))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_28]),c_0_29])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ r1_tsep_1(esk4_0,esk3_0)
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_29])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_48])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_68])]),c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_28]),c_0_60])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_65])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_28]),c_0_29])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_28]),c_0_29])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_28]),c_0_37])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_91,negated_conjecture,
    ( ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_89]),c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( ~ l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_28]),c_0_29])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_28]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.18/0.45  # and selection function SelectNewComplexAHP.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.029 s
% 0.18/0.45  # Presaturation interreduction done
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t40_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((((r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)=>(r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4)))&((r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4))=>r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)))&(r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))=>(r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3))))&((r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3))=>r1_tsep_1(X4,k1_tsep_1(X1,X2,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tmap_1)).
% 0.18/0.45  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.18/0.45  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.18/0.45  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.45  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.45  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.18/0.45  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.18/0.45  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.18/0.45  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((((r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)=>(r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4)))&((r1_tsep_1(X2,X4)&r1_tsep_1(X3,X4))=>r1_tsep_1(k1_tsep_1(X1,X2,X3),X4)))&(r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))=>(r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3))))&((r1_tsep_1(X4,X2)&r1_tsep_1(X4,X3))=>r1_tsep_1(X4,k1_tsep_1(X1,X2,X3))))))))), inference(assume_negation,[status(cth)],[t40_tmap_1])).
% 0.18/0.45  fof(c_0_9, plain, ![X17, X18, X19]:(((~v2_struct_0(k1_tsep_1(X17,X18,X19))|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17)))&(v1_pre_topc(k1_tsep_1(X17,X18,X19))|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17))))&(m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.18/0.45  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((((((r1_tsep_1(esk4_0,esk2_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))&(r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(((r1_tsep_1(esk4_0,esk2_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))&(r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))))&((((r1_tsep_1(esk4_0,esk2_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))&(r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(((r1_tsep_1(esk4_0,esk2_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))&(r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))))&((((r1_tsep_1(esk4_0,esk2_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))&(r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(((r1_tsep_1(esk4_0,esk2_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))&(r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))))))&((((((r1_tsep_1(esk4_0,esk2_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))&(r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(((r1_tsep_1(esk4_0,esk2_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))&(r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))))&((((r1_tsep_1(esk4_0,esk2_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk3_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))&(r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk3_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk3_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(((r1_tsep_1(esk4_0,esk2_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk3_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))&(r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk3_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk3_0,esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))))&((((r1_tsep_1(esk4_0,esk2_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))&(r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(((r1_tsep_1(esk4_0,esk2_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)))))&(r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))&(~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|(~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|(~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.18/0.45  fof(c_0_11, plain, ![X20, X21]:(~l1_struct_0(X20)|~l1_struct_0(X21)|(~r1_tsep_1(X20,X21)|r1_tsep_1(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.18/0.45  fof(c_0_12, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.45  cnf(c_0_13, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.45  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_18, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.45  cnf(c_0_19, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  fof(c_0_20, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.45  cnf(c_0_21, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_23, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 0.18/0.45  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  fof(c_0_26, plain, ![X11, X12, X13, X14]:((X14!=k1_tsep_1(X11,X12,X13)|u1_struct_0(X14)=k2_xboole_0(u1_struct_0(X12),u1_struct_0(X13))|(v2_struct_0(X14)|~v1_pre_topc(X14)|~m1_pre_topc(X14,X11))|(v2_struct_0(X13)|~m1_pre_topc(X13,X11))|(v2_struct_0(X12)|~m1_pre_topc(X12,X11))|(v2_struct_0(X11)|~l1_pre_topc(X11)))&(u1_struct_0(X14)!=k2_xboole_0(u1_struct_0(X12),u1_struct_0(X13))|X14=k1_tsep_1(X11,X12,X13)|(v2_struct_0(X14)|~v1_pre_topc(X14)|~m1_pre_topc(X14,X11))|(v2_struct_0(X13)|~m1_pre_topc(X13,X11))|(v2_struct_0(X12)|~m1_pre_topc(X12,X11))|(v2_struct_0(X11)|~l1_pre_topc(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.18/0.45  cnf(c_0_27, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk3_0,esk4_0)|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.45  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.45  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_15])])).
% 0.18/0.45  cnf(c_0_30, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.18/0.45  cnf(c_0_31, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_32, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.45  cnf(c_0_33, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.45  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.45  fof(c_0_35, plain, ![X15, X16]:((~r1_tsep_1(X15,X16)|r1_xboole_0(u1_struct_0(X15),u1_struct_0(X16))|~l1_struct_0(X16)|~l1_struct_0(X15))&(~r1_xboole_0(u1_struct_0(X15),u1_struct_0(X16))|r1_tsep_1(X15,X16)|~l1_struct_0(X16)|~l1_struct_0(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.18/0.45  cnf(c_0_36, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_37, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_30]), c_0_15])])).
% 0.18/0.45  cnf(c_0_38, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 0.18/0.45  cnf(c_0_39, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_13]), c_0_33]), c_0_34])).
% 0.18/0.45  cnf(c_0_40, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.45  cnf(c_0_41, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_37])])).
% 0.18/0.45  cnf(c_0_42, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_28]), c_0_29])])).
% 0.18/0.45  fof(c_0_43, plain, ![X5, X6, X7]:((r1_xboole_0(X5,k2_xboole_0(X6,X7))|~r1_xboole_0(X5,X6)|~r1_xboole_0(X5,X7))&((r1_xboole_0(X5,X6)|~r1_xboole_0(X5,k2_xboole_0(X6,X7)))&(r1_xboole_0(X5,X7)|~r1_xboole_0(X5,k2_xboole_0(X6,X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.18/0.45  cnf(c_0_44, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_14]), c_0_15])]), c_0_17]), c_0_16])).
% 0.18/0.45  cnf(c_0_45, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.45  cnf(c_0_46, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_37])])).
% 0.18/0.45  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.45  cnf(c_0_48, negated_conjecture, (k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_25])).
% 0.18/0.45  cnf(c_0_49, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk3_0,esk4_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_50, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 0.18/0.45  cnf(c_0_51, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk3_0))|~r1_xboole_0(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.45  cnf(c_0_52, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_28]), c_0_37])])).
% 0.18/0.45  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.45  cnf(c_0_54, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_55, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.45  cnf(c_0_56, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk3_0,esk4_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.45  cnf(c_0_57, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk2_0))|~r1_xboole_0(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.18/0.45  cnf(c_0_58, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_28]), c_0_37])])).
% 0.18/0.45  cnf(c_0_59, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_18])).
% 0.18/0.45  cnf(c_0_60, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_15])])).
% 0.18/0.45  cnf(c_0_61, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.45  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_28]), c_0_60])])).
% 0.18/0.45  cnf(c_0_63, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_61]), c_0_18])).
% 0.18/0.45  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_24]), c_0_15])])).
% 0.18/0.45  cnf(c_0_65, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_66, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_28]), c_0_64])])).
% 0.18/0.45  cnf(c_0_67, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_65])).
% 0.18/0.45  cnf(c_0_68, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_69, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_28]), c_0_60])])).
% 0.18/0.45  cnf(c_0_70, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 0.18/0.45  cnf(c_0_71, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_68])).
% 0.18/0.45  cnf(c_0_72, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.45  cnf(c_0_73, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_74, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_28]), c_0_64])])).
% 0.18/0.45  cnf(c_0_75, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_28]), c_0_64])])).
% 0.18/0.45  cnf(c_0_76, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),k2_xboole_0(X1,u1_struct_0(esk3_0)))|~r1_xboole_0(u1_struct_0(esk4_0),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.18/0.45  cnf(c_0_77, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_78, negated_conjecture, (~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.45  cnf(c_0_79, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_80, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_65])).
% 0.18/0.45  cnf(c_0_81, negated_conjecture, (r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_48])).
% 0.18/0.45  cnf(c_0_82, negated_conjecture, (~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|~r1_tsep_1(esk3_0,esk4_0)|~r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_68])]), c_0_79])])).
% 0.18/0.45  cnf(c_0_83, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_28]), c_0_60])])).
% 0.18/0.45  cnf(c_0_84, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_81])).
% 0.18/0.45  cnf(c_0_85, negated_conjecture, (~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|~r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_65])])).
% 0.18/0.45  cnf(c_0_86, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_87, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_88, negated_conjecture, (~r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.18/0.45  cnf(c_0_89, negated_conjecture, (r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_28]), c_0_37])])).
% 0.18/0.45  cnf(c_0_90, negated_conjecture, (~r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])])).
% 0.18/0.45  cnf(c_0_91, negated_conjecture, (~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_89]), c_0_90])).
% 0.18/0.45  cnf(c_0_92, negated_conjecture, (~l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_28]), c_0_29])])).
% 0.18/0.45  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_28]), c_0_37])]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 94
% 0.18/0.45  # Proof object clause steps            : 77
% 0.18/0.45  # Proof object formula steps           : 17
% 0.18/0.45  # Proof object conjectures             : 67
% 0.18/0.45  # Proof object clause conjectures      : 64
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 22
% 0.18/0.45  # Proof object initial formulas used   : 8
% 0.18/0.45  # Proof object generating inferences   : 50
% 0.18/0.45  # Proof object simplifying inferences  : 84
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 8
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 58
% 0.18/0.45  # Removed in clause preprocessing      : 27
% 0.18/0.45  # Initial clauses in saturation        : 31
% 0.18/0.45  # Processed clauses                    : 520
% 0.18/0.45  # ...of these trivial                  : 2
% 0.18/0.45  # ...subsumed                          : 10
% 0.18/0.45  # ...remaining for further processing  : 508
% 0.18/0.45  # Other redundant clauses eliminated   : 1
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 50
% 0.18/0.45  # Backward-rewritten                   : 45
% 0.18/0.45  # Generated clauses                    : 4239
% 0.18/0.45  # ...of the previous two non-trivial   : 4207
% 0.18/0.45  # Contextual simplify-reflections      : 7
% 0.18/0.45  # Paramodulations                      : 4238
% 0.18/0.45  # Factorizations                       : 0
% 0.18/0.45  # Equation resolutions                 : 1
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 381
% 0.18/0.45  #    Positive orientable unit clauses  : 76
% 0.18/0.45  #    Positive unorientable unit clauses: 0
% 0.18/0.45  #    Negative unit clauses             : 6
% 0.18/0.45  #    Non-unit-clauses                  : 299
% 0.18/0.45  # Current number of unprocessed clauses: 3740
% 0.18/0.45  # ...number of literals in the above   : 15534
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 126
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 10594
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 4792
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 67
% 0.18/0.45  # Unit Clause-clause subsumption calls : 305
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 62
% 0.18/0.45  # BW rewrite match successes           : 21
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 159897
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.110 s
% 0.18/0.45  # System time              : 0.011 s
% 0.18/0.45  # Total time               : 0.120 s
% 0.18/0.45  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
