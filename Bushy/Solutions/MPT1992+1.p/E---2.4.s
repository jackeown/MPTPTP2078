%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t41_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 151.30s
% Output     : CNFRefutation 151.30s
% Verified   : 
% Statistics : Number of formulae       :  153 (1195 expanded)
%              Number of clauses        :   95 ( 429 expanded)
%              Number of leaves         :   29 ( 303 expanded)
%              Depth                    :   30
%              Number of atoms          :  704 (11180 expanded)
%              Number of equality atoms :   33 (  80 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ( v1_waybel_3(k4_yellow_0(X1),X1)
       => ( ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & v1_finset_1(X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => ~ ( r1_waybel_3(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ~ ( r2_hidden(X3,X2)
                          & r3_orders_2(X1,X3,k4_yellow_0(X1)) ) ) ) )
          & ~ r2_subset_1(k4_waybel_0(X1,k12_waybel_0(X1,k3_subset_1(u1_struct_0(X1),k5_waybel_0(X1,k4_yellow_0(X1))))),k1_waybel_3(X1,k4_yellow_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t41_waybel_7)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t3_xboole_0)).

fof(redefinition_r2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r2_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',redefinition_r2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t7_boole)).

fof(cc10_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( v3_orders_2(X1)
          & v1_lattice3(X1)
          & v24_waybel_0(X1) )
       => ( v3_orders_2(X1)
          & v1_lattice3(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',cc10_waybel_0)).

fof(cc4_waybel_3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v3_waybel_3(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v24_waybel_0(X1)
          & v2_waybel_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',cc4_waybel_3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',cc2_lattice3)).

fof(t22_waybel_4,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => r2_hidden(k4_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t22_waybel_4)).

fof(fc11_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v13_waybel_0(k4_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc11_waybel_0)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k4_waybel_0)).

fof(fc16_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & v2_waybel_0(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v2_waybel_0(k4_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc16_waybel_0)).

fof(fc7_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_waybel_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc7_waybel_0)).

fof(fc22_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v2_waybel_0(k12_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc22_waybel_0)).

fof(dt_k12_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k12_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k12_waybel_0)).

fof(fc18_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k12_waybel_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc18_waybel_0)).

fof(fraenkel_a_2_0_waybel_3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_0_waybel_3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r1_waybel_3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fraenkel_a_2_0_waybel_3)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',existence_m1_subset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t2_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t6_boole)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k3_subset_1)).

fof(d3_waybel_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_waybel_3(X1,X2) = a_2_0_waybel_3(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',d3_waybel_3)).

fof(d2_waybel_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_waybel_3(X2,X1)
          <=> r1_waybel_3(X1,X2,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',d2_waybel_3)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_o_0_0_xboole_0)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k5_waybel_0)).

fof(dt_k4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k4_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',redefinition_r3_orders_2)).

fof(t45_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t45_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t4_subset)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_waybel_3(X1)
          & l1_orders_2(X1) )
       => ( v1_waybel_3(k4_yellow_0(X1),X1)
         => ( ! [X2] :
                ( ( ~ v1_xboole_0(X2)
                  & v1_finset_1(X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
               => ~ ( r1_waybel_3(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X1))
                       => ~ ( r2_hidden(X3,X2)
                            & r3_orders_2(X1,X3,k4_yellow_0(X1)) ) ) ) )
            & ~ r2_subset_1(k4_waybel_0(X1,k12_waybel_0(X1,k3_subset_1(u1_struct_0(X1),k5_waybel_0(X1,k4_yellow_0(X1))))),k1_waybel_3(X1,k4_yellow_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_waybel_7])).

fof(c_0_30,plain,(
    ! [X87,X88,X90,X91,X92] :
      ( ( r2_hidden(esk10_2(X87,X88),X87)
        | r1_xboole_0(X87,X88) )
      & ( r2_hidden(esk10_2(X87,X88),X88)
        | r1_xboole_0(X87,X88) )
      & ( ~ r2_hidden(X92,X90)
        | ~ r2_hidden(X92,X91)
        | ~ r1_xboole_0(X90,X91) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_31,plain,(
    ! [X63,X64] :
      ( ( ~ r2_subset_1(X63,X64)
        | r1_xboole_0(X63,X64)
        | v1_xboole_0(X63)
        | v1_xboole_0(X64) )
      & ( ~ r1_xboole_0(X63,X64)
        | r2_subset_1(X63,X64)
        | v1_xboole_0(X63)
        | v1_xboole_0(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r2_subset_1])])])])).

fof(c_0_32,plain,(
    ! [X103,X104] :
      ( ~ r2_hidden(X103,X104)
      | ~ v1_xboole_0(X104) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_33,plain,(
    ! [X107] :
      ( ( v3_orders_2(X107)
        | ~ v3_orders_2(X107)
        | ~ v1_lattice3(X107)
        | ~ v24_waybel_0(X107)
        | ~ l1_orders_2(X107) )
      & ( v1_lattice3(X107)
        | ~ v3_orders_2(X107)
        | ~ v1_lattice3(X107)
        | ~ v24_waybel_0(X107)
        | ~ l1_orders_2(X107) )
      & ( v2_yellow_0(X107)
        | ~ v3_orders_2(X107)
        | ~ v1_lattice3(X107)
        | ~ v24_waybel_0(X107)
        | ~ l1_orders_2(X107) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc10_waybel_0])])])).

fof(c_0_34,plain,(
    ! [X109] :
      ( ( ~ v2_struct_0(X109)
        | v2_struct_0(X109)
        | ~ v3_orders_2(X109)
        | ~ v3_waybel_3(X109)
        | ~ l1_orders_2(X109) )
      & ( v3_orders_2(X109)
        | v2_struct_0(X109)
        | ~ v3_orders_2(X109)
        | ~ v3_waybel_3(X109)
        | ~ l1_orders_2(X109) )
      & ( v24_waybel_0(X109)
        | v2_struct_0(X109)
        | ~ v3_orders_2(X109)
        | ~ v3_waybel_3(X109)
        | ~ l1_orders_2(X109) )
      & ( v2_waybel_3(X109)
        | v2_struct_0(X109)
        | ~ v3_orders_2(X109)
        | ~ v3_waybel_3(X109)
        | ~ l1_orders_2(X109) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_waybel_3])])])])).

fof(c_0_35,plain,(
    ! [X108] :
      ( ~ l1_orders_2(X108)
      | ~ v2_lattice3(X108)
      | ~ v2_struct_0(X108) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_36,negated_conjecture,(
    ! [X7] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v1_lattice3(esk1_0)
      & v2_lattice3(esk1_0)
      & v3_waybel_3(esk1_0)
      & l1_orders_2(esk1_0)
      & v1_waybel_3(k4_yellow_0(esk1_0),esk1_0)
      & ( ~ v1_xboole_0(esk2_0)
        | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) )
      & ( v1_finset_1(esk2_0)
        | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) )
      & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) )
      & ( r1_waybel_3(esk1_0,k2_yellow_0(esk1_0,esk2_0),k4_yellow_0(esk1_0))
        | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) )
      & ( ~ m1_subset_1(X7,u1_struct_0(esk1_0))
        | ~ r2_hidden(X7,esk2_0)
        | ~ r3_orders_2(esk1_0,X7,k4_yellow_0(esk1_0))
        | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r2_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X77,X78] :
      ( v2_struct_0(X77)
      | ~ v3_orders_2(X77)
      | ~ v4_orders_2(X77)
      | ~ v5_orders_2(X77)
      | ~ v2_yellow_0(X77)
      | ~ l1_orders_2(X77)
      | v1_xboole_0(X78)
      | ~ v2_waybel_0(X78,X77)
      | ~ v13_waybel_0(X78,X77)
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))
      | r2_hidden(k4_yellow_0(X77),X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_waybel_4])])])])).

fof(c_0_41,plain,(
    ! [X110,X111] :
      ( v2_struct_0(X110)
      | ~ v4_orders_2(X110)
      | ~ l1_orders_2(X110)
      | ~ m1_subset_1(X111,k1_zfmisc_1(u1_struct_0(X110)))
      | v13_waybel_0(k4_waybel_0(X110,X111),X110) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc11_waybel_0])])])).

fof(c_0_42,plain,(
    ! [X24,X25] :
      ( ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k4_waybel_0(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

cnf(c_0_43,plain,
    ( v2_yellow_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v24_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v24_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( ~ r2_subset_1(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k4_yellow_0(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v13_waybel_0(k4_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v2_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_waybel_3(X1)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( v3_waybel_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ r2_hidden(X1,k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_yellow_0(X1),k4_waybel_0(X1,X2))
    | v1_xboole_0(k4_waybel_0(X1,X2))
    | ~ v2_waybel_0(k4_waybel_0(X1,X2),X1)
    | ~ v2_yellow_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v2_yellow_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_47]),c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_63,plain,(
    ! [X112,X113] :
      ( v2_struct_0(X112)
      | ~ v3_orders_2(X112)
      | ~ v4_orders_2(X112)
      | ~ l1_orders_2(X112)
      | ~ v2_waybel_0(X113,X112)
      | ~ m1_subset_1(X113,k1_zfmisc_1(u1_struct_0(X112)))
      | v2_waybel_0(k4_waybel_0(X112,X113),X112) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc16_waybel_0])])])).

fof(c_0_64,plain,(
    ! [X119,X120] :
      ( v2_struct_0(X119)
      | ~ v3_orders_2(X119)
      | ~ l1_orders_2(X119)
      | v1_xboole_0(X120)
      | ~ m1_subset_1(X120,k1_zfmisc_1(u1_struct_0(X119)))
      | ~ v1_xboole_0(k4_waybel_0(X119,X120)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_waybel_0])])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ v2_waybel_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_47]),c_0_61]),c_0_62]),c_0_56])]),c_0_57])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_waybel_0(k4_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_waybel_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ v2_waybel_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_47]),c_0_62]),c_0_56])]),c_0_57])).

fof(c_0_69,plain,(
    ! [X116,X117] :
      ( ~ v3_orders_2(X116)
      | ~ v4_orders_2(X116)
      | ~ v5_orders_2(X116)
      | ~ v2_lattice3(X116)
      | ~ l1_orders_2(X116)
      | ~ m1_subset_1(X117,k1_zfmisc_1(u1_struct_0(X116)))
      | v2_waybel_0(k12_waybel_0(X116,X117),X116) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc22_waybel_0])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ v2_waybel_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_47]),c_0_56])]),c_0_57])).

cnf(c_0_71,plain,
    ( v2_waybel_0(k12_waybel_0(X1,X2),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_72,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | m1_subset_1(k12_waybel_0(X14,X15),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k12_waybel_0])])])).

fof(c_0_73,plain,(
    ! [X114,X115] :
      ( v2_struct_0(X114)
      | ~ v5_orders_2(X114)
      | ~ v2_yellow_0(X114)
      | ~ l1_orders_2(X114)
      | ~ m1_subset_1(X115,k1_zfmisc_1(u1_struct_0(X114)))
      | ~ v1_xboole_0(k12_waybel_0(X114,X115)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc18_waybel_0])])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_47]),c_0_46]),c_0_61]),c_0_62]),c_0_56])])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k12_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_76,plain,(
    ! [X44,X45,X46,X48] :
      ( ( m1_subset_1(esk7_3(X44,X45,X46),u1_struct_0(X45))
        | ~ r2_hidden(X44,a_2_0_waybel_3(X45,X46))
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ l1_orders_2(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) )
      & ( X44 = esk7_3(X44,X45,X46)
        | ~ r2_hidden(X44,a_2_0_waybel_3(X45,X46))
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ l1_orders_2(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) )
      & ( r1_waybel_3(X45,esk7_3(X44,X45,X46),X46)
        | ~ r2_hidden(X44,a_2_0_waybel_3(X45,X46))
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ l1_orders_2(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) )
      & ( ~ m1_subset_1(X48,u1_struct_0(X45))
        | X44 != X48
        | ~ r1_waybel_3(X45,X48,X46)
        | r2_hidden(X44,a_2_0_waybel_3(X45,X46))
        | v2_struct_0(X45)
        | ~ v3_orders_2(X45)
        | ~ l1_orders_2(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_waybel_3])])])])])])).

fof(c_0_77,plain,(
    ! [X99,X100,X101] :
      ( ~ r2_hidden(X99,X100)
      | ~ m1_subset_1(X100,k1_zfmisc_1(X101))
      | ~ v1_xboole_0(X101) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_78,plain,(
    ! [X39] : m1_subset_1(esk5_1(X39),X39) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_79,plain,(
    ! [X81,X82] :
      ( ( ~ r2_hidden(esk9_2(X81,X82),X81)
        | ~ r2_hidden(esk9_2(X81,X82),X82)
        | X81 = X82 )
      & ( r2_hidden(esk9_2(X81,X82),X81)
        | r2_hidden(esk9_2(X81,X82),X82)
        | X81 = X82 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_80,plain,(
    ! [X102] :
      ( ~ v1_xboole_0(X102)
      | X102 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k12_waybel_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47])]),c_0_57])).

fof(c_0_83,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | m1_subset_1(k3_subset_1(X20,X21),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_84,plain,
    ( r2_hidden(X3,a_2_0_waybel_3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r1_waybel_3(X2,X1,X4)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_85,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | k1_waybel_3(X12,X13) = a_2_0_waybel_3(X12,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_waybel_3])])])])).

fof(c_0_86,plain,(
    ! [X10,X11] :
      ( ( ~ v1_waybel_3(X11,X10)
        | r1_waybel_3(X10,X11,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_waybel_3(X10,X11,X11)
        | v1_waybel_3(X11,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v3_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_waybel_3])])])])])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_89,plain,
    ( r2_hidden(esk9_2(X1,X2),X1)
    | r2_hidden(esk9_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_60]),c_0_47]),c_0_61])]),c_0_57])).

cnf(c_0_93,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_waybel_3(X1,X3))
    | ~ r1_waybel_3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | k1_waybel_3(X1,X2) = a_2_0_waybel_3(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( r1_waybel_3(X2,X1,X1)
    | v2_struct_0(X2)
    | ~ v1_waybel_3(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( v1_waybel_3(k4_yellow_0(esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,esk5_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_99,plain,
    ( X1 = X2
    | r2_hidden(esk9_2(X1,X2),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_89])).

cnf(c_0_100,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_102,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_waybel_3(X1,X3))
    | ~ r1_waybel_3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( r1_waybel_3(esk1_0,k4_yellow_0(esk1_0),k4_yellow_0(esk1_0))
    | ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_47]),c_0_56])]),c_0_57])).

fof(c_0_104,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | m1_subset_1(k5_waybel_0(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_105,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_106,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_47]),c_0_56])]),c_0_57]),c_0_103])).

cnf(c_0_108,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

fof(c_0_109,plain,(
    ! [X26] :
      ( ~ l1_orders_2(X26)
      | m1_subset_1(k4_yellow_0(X26),u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

cnf(c_0_110,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

fof(c_0_111,plain,(
    ! [X65,X66,X67] :
      ( ( ~ r3_orders_2(X65,X66,X67)
        | r1_orders_2(X65,X66,X67)
        | v2_struct_0(X65)
        | ~ v3_orders_2(X65)
        | ~ l1_orders_2(X65)
        | ~ m1_subset_1(X66,u1_struct_0(X65))
        | ~ m1_subset_1(X67,u1_struct_0(X65)) )
      & ( ~ r1_orders_2(X65,X66,X67)
        | r3_orders_2(X65,X66,X67)
        | v2_struct_0(X65)
        | ~ v3_orders_2(X65)
        | ~ l1_orders_2(X65)
        | ~ m1_subset_1(X66,u1_struct_0(X65))
        | ~ m1_subset_1(X67,u1_struct_0(X65)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_112,plain,(
    ! [X93,X94] :
      ( v2_struct_0(X93)
      | ~ v5_orders_2(X93)
      | ~ v2_yellow_0(X93)
      | ~ l1_orders_2(X93)
      | ~ m1_subset_1(X94,u1_struct_0(X93))
      | r1_orders_2(X93,X94,k4_yellow_0(X93)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

fof(c_0_113,plain,(
    ! [X96,X97,X98] :
      ( ~ r2_hidden(X96,X97)
      | ~ m1_subset_1(X97,k1_zfmisc_1(X98))
      | m1_subset_1(X96,X98) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_47])]),c_0_57])).

cnf(c_0_115,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_110])).

cnf(c_0_117,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_118,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_119,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_47])])).

cnf(c_0_121,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk9_2(k1_xboole_0,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_116,c_0_89])).

cnf(c_0_122,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0)
    | ~ r3_orders_2(esk1_0,X1,k4_yellow_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_123,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_125,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk9_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_106])).

cnf(c_0_126,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_60]),c_0_47]),c_0_61]),c_0_56])]),c_0_57])).

cnf(c_0_127,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | m1_subset_1(esk9_2(k1_xboole_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_125]),c_0_127])).

cnf(c_0_129,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_130,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ r2_hidden(X1,k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ r2_hidden(X1,k1_waybel_3(esk1_0,k4_yellow_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( ~ r2_hidden(X1,k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ r2_hidden(X1,k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ v2_waybel_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_59]),c_0_60]),c_0_47]),c_0_61]),c_0_62]),c_0_56])]),c_0_57])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ v2_waybel_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_59]),c_0_60]),c_0_47]),c_0_61]),c_0_62]),c_0_56])]),c_0_57])).

cnf(c_0_134,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ v2_waybel_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_66]),c_0_47]),c_0_62]),c_0_56])]),c_0_57])).

cnf(c_0_135,negated_conjecture,
    ( v1_xboole_0(k4_waybel_0(esk1_0,k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))))))
    | ~ v2_waybel_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_66]),c_0_47]),c_0_62]),c_0_56])]),c_0_57])).

cnf(c_0_136,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ v2_waybel_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_134]),c_0_47]),c_0_56])]),c_0_57])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ v2_waybel_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),esk1_0)
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_135]),c_0_47]),c_0_56])]),c_0_57])).

cnf(c_0_138,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_71]),c_0_47]),c_0_46]),c_0_61]),c_0_62]),c_0_56])])).

cnf(c_0_139,negated_conjecture,
    ( v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_71]),c_0_47]),c_0_46]),c_0_61]),c_0_62]),c_0_56])])).

cnf(c_0_140,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_75]),c_0_47])]),c_0_57])).

cnf(c_0_141,negated_conjecture,
    ( v1_xboole_0(k12_waybel_0(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)))))
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_75]),c_0_47])]),c_0_57])).

cnf(c_0_142,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_140]),c_0_60]),c_0_47]),c_0_61])]),c_0_57])).

cnf(c_0_143,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k5_waybel_0(esk1_0,k4_yellow_0(esk1_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_141]),c_0_60]),c_0_47]),c_0_61])]),c_0_57])).

cnf(c_0_144,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_93])).

cnf(c_0_145,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_0(esk1_0),k1_waybel_3(esk1_0,k4_yellow_0(esk1_0)))
    | ~ m1_subset_1(k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_93])).

cnf(c_0_146,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ m1_subset_1(k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_102]),c_0_47]),c_0_56])]),c_0_57]),c_0_103])).

cnf(c_0_147,negated_conjecture,
    ( ~ m1_subset_1(k5_waybel_0(esk1_0,k4_yellow_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_102]),c_0_47]),c_0_56])]),c_0_57]),c_0_103])).

cnf(c_0_148,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_108]),c_0_47])]),c_0_57])).

cnf(c_0_149,negated_conjecture,
    ( ~ m1_subset_1(k4_yellow_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_108]),c_0_47])]),c_0_57])).

cnf(c_0_150,negated_conjecture,
    ( k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_115]),c_0_47])])).

cnf(c_0_151,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_115]),c_0_47])])).

cnf(c_0_152,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_150]),c_0_151]),
    [proof]).
%------------------------------------------------------------------------------
