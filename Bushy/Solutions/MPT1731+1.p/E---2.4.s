%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t40_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 160.55s
% Output     : CNFRefutation 160.55s
% Verified   : 
% Statistics : Number of formulae       :  126 (2941 expanded)
%              Number of clauses        :   96 (1230 expanded)
%              Number of leaves         :   15 ( 689 expanded)
%              Depth                    :   24
%              Number of atoms          :  560 (84972 expanded)
%              Number of equality atoms :   46 ( 345 expanded)
%              Maximal formula depth    :   51 (   4 average)
%              Maximal clause size      :  189 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t40_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_k1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_l1_pre_topc)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',symmetry_r1_tsep_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',d3_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',d2_tsep_1)).

fof(fc5_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',fc5_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t23_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',commutativity_k3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',commutativity_k2_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',dt_o_0_0_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t40_tmap_1.p',t1_boole)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v2_struct_0(k1_tsep_1(X35,X36,X37))
        | v2_struct_0(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35) )
      & ( v1_pre_topc(k1_tsep_1(X35,X36,X37))
        | v2_struct_0(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35) )
      & ( m1_pre_topc(k1_tsep_1(X35,X36,X37),X35)
        | v2_struct_0(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_17,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | l1_pre_topc(X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,X2),esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | l1_struct_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_33,plain,(
    ! [X72,X73] :
      ( ~ l1_struct_0(X72)
      | ~ l1_struct_0(X73)
      | ~ r1_tsep_1(X72,X73)
      | r1_tsep_1(X73,X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_34,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_38,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ( ~ r1_tsep_1(X29,X30)
        | r1_xboole_0(u1_struct_0(X29),u1_struct_0(X30))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X29) )
      & ( ~ r1_xboole_0(u1_struct_0(X29),u1_struct_0(X30))
        | r1_tsep_1(X29,X30)
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_42,negated_conjecture,
    ( l1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tsep_1(esk2_0,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

fof(c_0_45,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X28 != k1_tsep_1(X25,X26,X27)
        | u1_struct_0(X28) = k2_xboole_0(u1_struct_0(X26),u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) )
      & ( u1_struct_0(X28) != k2_xboole_0(u1_struct_0(X26),u1_struct_0(X27))
        | X28 = k1_tsep_1(X25,X26,X27)
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

cnf(c_0_46,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_51])).

fof(c_0_59,plain,(
    ! [X100,X101] :
      ( v1_xboole_0(X100)
      | ~ v1_xboole_0(k2_xboole_0(X101,X100)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_xboole_0])])])).

fof(c_0_60,plain,(
    ! [X81,X82,X83] : k3_xboole_0(X81,k2_xboole_0(X82,X83)) = k2_xboole_0(k3_xboole_0(X81,X82),k3_xboole_0(X81,X83)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_61,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_18]),c_0_53]),c_0_54])).

fof(c_0_62,plain,(
    ! [X31,X32] :
      ( ( ~ r1_xboole_0(X31,X32)
        | k3_xboole_0(X31,X32) = k1_xboole_0 )
      & ( k3_xboole_0(X31,X32) != k1_xboole_0
        | r1_xboole_0(X31,X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0))
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_65,plain,(
    ! [X17,X18] : k3_xboole_0(X17,X18) = k3_xboole_0(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_58])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_69,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k2_xboole_0(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(esk1_0,X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_19]),c_0_20])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0))
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X95] :
      ( ~ v1_xboole_0(X95)
      | X95 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_39])).

cnf(c_0_77,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_xboole_0(k3_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_23]),c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k1_xboole_0
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_84,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_75]),c_0_76])).

cnf(c_0_85,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_27]),c_0_28])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k1_xboole_0
    | r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

fof(c_0_89,plain,(
    ! [X76] : k2_xboole_0(X76,k1_xboole_0) = X76 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_90,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(k3_xboole_0(X1,u1_struct_0(esk2_0)))
    | ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k1_xboole_0
    | k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_87]),c_0_73])).

cnf(c_0_93,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_88])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0))
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])]),c_0_82])).

cnf(c_0_97,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_94,c_0_78])).

cnf(c_0_98,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_99,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_100,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k1_xboole_0
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_95]),c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),k2_xboole_0(u1_struct_0(esk2_0),X1)) = k3_xboole_0(u1_struct_0(esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_96]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_40])).

cnf(c_0_103,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k1_xboole_0
    | r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_86])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_73])).

cnf(c_0_107,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_39])).

cnf(c_0_108,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_96])).

cnf(c_0_109,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_58])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_39])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ r1_tsep_1(esk4_0,esk3_0)
    | ~ r1_tsep_1(k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_115,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_111])])).

cnf(c_0_116,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_58])).

cnf(c_0_117,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_118,negated_conjecture,
    ( r1_tsep_1(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_42])).

cnf(c_0_119,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_105,c_0_110])).

cnf(c_0_120,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_111])]),c_0_115])]),c_0_116]),c_0_56])).

cnf(c_0_121,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_117])])).

cnf(c_0_122,negated_conjecture,
    ( r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_39])).

cnf(c_0_123,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121])])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])]),c_0_124]),
    [proof]).
%------------------------------------------------------------------------------
