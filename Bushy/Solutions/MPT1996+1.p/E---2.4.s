%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t45_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 284.96s
% Output     : CNFRefutation 284.96s
% Verified   : 
% Statistics : Number of formulae       :   93 (1127 expanded)
%              Number of clauses        :   66 ( 367 expanded)
%              Number of leaves         :   13 ( 279 expanded)
%              Depth                    :   18
%              Number of atoms          :  679 (16362 expanded)
%              Number of equality atoms :   22 ( 114 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal clause size      :   67 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v5_waybel_4(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
         => ( v5_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ( ( r2_hidden(k7_yellow_3(X1,X1,X3,X5),X2)
                                & r2_hidden(k7_yellow_3(X1,X1,X4,X6),X2) )
                             => r2_hidden(k7_yellow_3(X1,X1,k12_lattice3(X1,X3,X4),k12_lattice3(X1,X5,X6)),X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',t45_waybel_7)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',redefinition_k12_lattice3)).

fof(d7_waybel_7,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
         => ( v5_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( ( r2_hidden(k7_yellow_3(X1,X1,X3,X4),X2)
                            & r2_hidden(k7_yellow_3(X1,X1,X3,X5),X2) )
                         => r2_hidden(k7_yellow_3(X1,X1,X3,k11_lattice3(X1,X4,X5)),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',d7_waybel_7)).

fof(redefinition_k7_yellow_3,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X4,u1_struct_0(X2)) )
     => k7_yellow_3(X1,X2,X3,X4) = k4_tarski(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',redefinition_k7_yellow_3)).

fof(d5_waybel_4,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
         => ( v2_waybel_4(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X6,X3)
                                & r2_hidden(k4_tarski(X3,X4),X2)
                                & r1_orders_2(X1,X4,X5) )
                             => r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',d5_waybel_4)).

fof(cc1_waybel_4,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
         => ( v5_waybel_4(X2,X1)
           => ( v1_waybel_4(X2,X1)
              & v2_waybel_4(X2,X1)
              & v3_waybel_4(X2,X1)
              & v4_waybel_4(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',cc1_waybel_4)).

fof(t23_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k12_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',t23_yellow_0)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',dt_k12_lattice3)).

fof(t25_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k12_lattice3(X1,X2,X3)
              <=> r3_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',t25_yellow_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',reflexivity_r3_orders_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',existence_m1_subset_1)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',cc2_lattice3)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',redefinition_r3_orders_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( v5_waybel_4(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
           => ( v5_waybel_7(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ( ( r2_hidden(k7_yellow_3(X1,X1,X3,X5),X2)
                                  & r2_hidden(k7_yellow_3(X1,X1,X4,X6),X2) )
                               => r2_hidden(k7_yellow_3(X1,X1,k12_lattice3(X1,X3,X4),k12_lattice3(X1,X5,X6)),X2) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_waybel_7])).

fof(c_0_14,negated_conjecture,(
    ! [X13,X14,X15,X16] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v1_yellow_0(esk1_0)
      & v1_lattice3(esk1_0)
      & v2_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & v5_waybel_4(esk2_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( m1_subset_1(esk5_0,u1_struct_0(esk1_0))
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( m1_subset_1(esk6_0,u1_struct_0(esk1_0))
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk3_0,esk5_0),esk2_0)
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk4_0,esk6_0),esk2_0)
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),k12_lattice3(esk1_0,esk5_0,esk6_0)),esk2_0)
        | ~ v5_waybel_7(esk2_0,esk1_0) )
      & ( v5_waybel_7(esk2_0,esk1_0)
        | ~ m1_subset_1(X13,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X14,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X15,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X16,u1_struct_0(esk1_0))
        | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X13,X15),esk2_0)
        | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X14,X16),esk2_0)
        | r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,X13,X14),k12_lattice3(esk1_0,X15,X16)),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

fof(c_0_15,plain,(
    ! [X65,X66,X67] :
      ( ~ v5_orders_2(X65)
      | ~ v2_lattice3(X65)
      | ~ l1_orders_2(X65)
      | ~ m1_subset_1(X66,u1_struct_0(X65))
      | ~ m1_subset_1(X67,u1_struct_0(X65))
      | k12_lattice3(X65,X66,X67) = k11_lattice3(X65,X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),k12_lattice3(esk1_0,esk5_0,esk6_0)),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0))
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( ~ v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ r2_hidden(k7_yellow_3(X33,X33,X35,X36),X34)
        | ~ r2_hidden(k7_yellow_3(X33,X33,X35,X37),X34)
        | r2_hidden(k7_yellow_3(X33,X33,X35,k11_lattice3(X33,X36,X37)),X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) )
      & ( m1_subset_1(esk11_2(X33,X34),u1_struct_0(X33))
        | v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) )
      & ( m1_subset_1(esk12_2(X33,X34),u1_struct_0(X33))
        | v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) )
      & ( m1_subset_1(esk13_2(X33,X34),u1_struct_0(X33))
        | v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(k7_yellow_3(X33,X33,esk11_2(X33,X34),esk12_2(X33,X34)),X34)
        | v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(k7_yellow_3(X33,X33,esk11_2(X33,X34),esk13_2(X33,X34)),X34)
        | v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) )
      & ( ~ r2_hidden(k7_yellow_3(X33,X33,esk11_2(X33,X34),k11_lattice3(X33,esk12_2(X33,X34),esk13_2(X33,X34))),X34)
        | v5_waybel_7(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_7])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),k11_lattice3(esk1_0,esk5_0,esk6_0)),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(k7_yellow_3(X2,X2,X3,k11_lattice3(X2,X4,X5)),X1)
    | v2_struct_0(X2)
    | ~ v5_waybel_7(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ r2_hidden(k7_yellow_3(X2,X2,X3,X4),X1)
    | ~ r2_hidden(k7_yellow_3(X2,X2,X3,X5),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X68,X69,X70,X71] :
      ( v2_struct_0(X68)
      | ~ l1_orders_2(X68)
      | v2_struct_0(X69)
      | ~ l1_orders_2(X69)
      | ~ m1_subset_1(X70,u1_struct_0(X68))
      | ~ m1_subset_1(X71,u1_struct_0(X69))
      | k7_yellow_3(X68,X69,X70,X71) = k4_tarski(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_yellow_3])])])).

fof(c_0_28,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X28,u1_struct_0(X23))
        | ~ r1_orders_2(X23,X28,X25)
        | ~ r2_hidden(k4_tarski(X25,X26),X24)
        | ~ r1_orders_2(X23,X26,X27)
        | r2_hidden(k4_tarski(X28,X27),X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk7_2(X23,X24),u1_struct_0(X23))
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk8_2(X23,X24),u1_struct_0(X23))
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk9_2(X23,X24),u1_struct_0(X23))
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk10_2(X23,X24),u1_struct_0(X23))
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk10_2(X23,X24),esk7_2(X23,X24))
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(k4_tarski(esk7_2(X23,X24),esk8_2(X23,X24)),X24)
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk8_2(X23,X24),esk9_2(X23,X24))
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) )
      & ( ~ r2_hidden(k4_tarski(esk10_2(X23,X24),esk9_2(X23,X24)),X24)
        | v2_waybel_4(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_4])])])])])).

fof(c_0_29,plain,(
    ! [X104,X105] :
      ( ( v1_waybel_4(X105,X104)
        | ~ v5_waybel_4(X105,X104)
        | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X104),u1_struct_0(X104))))
        | v2_struct_0(X104)
        | ~ l1_orders_2(X104) )
      & ( v2_waybel_4(X105,X104)
        | ~ v5_waybel_4(X105,X104)
        | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X104),u1_struct_0(X104))))
        | v2_struct_0(X104)
        | ~ l1_orders_2(X104) )
      & ( v3_waybel_4(X105,X104)
        | ~ v5_waybel_4(X105,X104)
        | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X104),u1_struct_0(X104))))
        | v2_struct_0(X104)
        | ~ l1_orders_2(X104) )
      & ( v4_waybel_4(X105,X104)
        | ~ v5_waybel_4(X105,X104)
        | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X104),u1_struct_0(X104))))
        | v2_struct_0(X104)
        | ~ l1_orders_2(X104) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_waybel_4])])])])])).

cnf(c_0_30,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk6_0),esk2_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk5_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_18])]),c_0_21]),c_0_22])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k7_yellow_3(X1,X2,X3,X4) = k4_tarski(X3,X4)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X6,X5),X1)
    | ~ v2_waybel_4(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X6,X3)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r1_orders_2(X2,X4,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk4_0,esk6_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( v2_waybel_4(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_waybel_4(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v5_waybel_4(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk5_0),esk2_0)
    | ~ r2_hidden(k4_tarski(k12_lattice3(esk1_0,esk3_0,esk4_0),esk6_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_18])]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ r1_orders_2(esk1_0,X4,X2)
    | ~ v2_waybel_4(esk2_0,esk1_0)
    | ~ r2_hidden(k4_tarski(X3,X4),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_18])])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r2_hidden(k4_tarski(esk4_0,esk6_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_18])]),c_0_34]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v2_waybel_4(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_36]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk3_0,esk5_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r2_hidden(k4_tarski(k12_lattice3(esk1_0,esk3_0,esk4_0),esk5_0),esk2_0)
    | ~ r2_hidden(k4_tarski(k12_lattice3(esk1_0,esk3_0,esk4_0),esk6_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_18])]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r2_hidden(k4_tarski(X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk6_0,X2)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34]),c_0_22]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r2_hidden(k4_tarski(esk3_0,esk5_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_18])]),c_0_42]),c_0_21])).

fof(c_0_46,plain,(
    ! [X80,X81,X82,X83,X84] :
      ( ( r1_orders_2(X80,X83,X81)
        | X83 != k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) )
      & ( r1_orders_2(X80,X83,X82)
        | X83 != k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) )
      & ( ~ m1_subset_1(X84,u1_struct_0(X80))
        | ~ r1_orders_2(X80,X84,X81)
        | ~ r1_orders_2(X80,X84,X82)
        | r1_orders_2(X80,X84,X83)
        | X83 != k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) )
      & ( m1_subset_1(esk17_4(X80,X81,X82,X83),u1_struct_0(X80))
        | ~ r1_orders_2(X80,X83,X81)
        | ~ r1_orders_2(X80,X83,X82)
        | X83 = k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) )
      & ( r1_orders_2(X80,esk17_4(X80,X81,X82,X83),X81)
        | ~ r1_orders_2(X80,X83,X81)
        | ~ r1_orders_2(X80,X83,X82)
        | X83 = k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) )
      & ( r1_orders_2(X80,esk17_4(X80,X81,X82,X83),X82)
        | ~ r1_orders_2(X80,X83,X81)
        | ~ r1_orders_2(X80,X83,X82)
        | X83 = k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) )
      & ( ~ r1_orders_2(X80,esk17_4(X80,X81,X82,X83),X83)
        | ~ r1_orders_2(X80,X83,X81)
        | ~ r1_orders_2(X80,X83,X82)
        | X83 = k12_lattice3(X80,X81,X82)
        | ~ m1_subset_1(X83,u1_struct_0(X80))
        | ~ m1_subset_1(X82,u1_struct_0(X80))
        | ~ m1_subset_1(X81,u1_struct_0(X80))
        | ~ v5_orders_2(X80)
        | ~ v2_lattice3(X80)
        | ~ l1_orders_2(X80) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).

fof(c_0_47,plain,(
    ! [X46,X47,X48] :
      ( ~ v5_orders_2(X46)
      | ~ v2_lattice3(X46)
      | ~ l1_orders_2(X46)
      | ~ m1_subset_1(X47,u1_struct_0(X46))
      | ~ m1_subset_1(X48,u1_struct_0(X46))
      | m1_subset_1(k12_lattice3(X46,X47,X48),u1_struct_0(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk1_0,esk6_0,esk6_0)
    | ~ r2_hidden(k4_tarski(k12_lattice3(esk1_0,esk3_0,esk4_0),esk5_0),esk2_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r2_hidden(k4_tarski(X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,esk5_0,X2)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_42]),c_0_21]),c_0_40])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_52,plain,(
    ! [X86,X87,X88] :
      ( ( X87 != k12_lattice3(X86,X87,X88)
        | r3_orders_2(X86,X87,X88)
        | ~ m1_subset_1(X88,u1_struct_0(X86))
        | ~ m1_subset_1(X87,u1_struct_0(X86))
        | ~ v3_orders_2(X86)
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) )
      & ( ~ r3_orders_2(X86,X87,X88)
        | X87 = k12_lattice3(X86,X87,X88)
        | ~ m1_subset_1(X88,u1_struct_0(X86))
        | ~ m1_subset_1(X87,u1_struct_0(X86))
        | ~ v3_orders_2(X86)
        | ~ v5_orders_2(X86)
        | ~ v2_lattice3(X86)
        | ~ l1_orders_2(X86) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

fof(c_0_53,plain,(
    ! [X75,X76,X77] :
      ( v2_struct_0(X75)
      | ~ v3_orders_2(X75)
      | ~ l1_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ m1_subset_1(X77,u1_struct_0(X75))
      | r3_orders_2(X75,X76,X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_54,plain,(
    ! [X59] : m1_subset_1(esk16_1(X59),X59) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk3_0)
    | ~ r1_orders_2(esk1_0,esk6_0,esk6_0)
    | ~ r1_orders_2(esk1_0,esk5_0,esk5_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_21])).

cnf(c_0_56,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( X2 = k12_lattice3(X1,X2,X3)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk16_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_61,plain,(
    ! [X106] :
      ( ~ l1_orders_2(X106)
      | ~ v2_lattice3(X106)
      | ~ v2_struct_0(X106) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r1_orders_2(esk1_0,k12_lattice3(esk1_0,esk3_0,esk4_0),esk3_0)
    | ~ r1_orders_2(esk1_0,esk6_0,esk6_0)
    | ~ r1_orders_2(esk1_0,esk5_0,esk5_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_18]),c_0_19]),c_0_20])]),c_0_34]),c_0_42])).

cnf(c_0_63,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]),c_0_51])).

fof(c_0_64,plain,(
    ! [X72,X73,X74] :
      ( ( ~ r3_orders_2(X72,X73,X74)
        | r1_orders_2(X72,X73,X74)
        | v2_struct_0(X72)
        | ~ v3_orders_2(X72)
        | ~ l1_orders_2(X72)
        | ~ m1_subset_1(X73,u1_struct_0(X72))
        | ~ m1_subset_1(X74,u1_struct_0(X72)) )
      & ( ~ r1_orders_2(X72,X73,X74)
        | r3_orders_2(X72,X73,X74)
        | v2_struct_0(X72)
        | ~ v3_orders_2(X72)
        | ~ l1_orders_2(X72)
        | ~ m1_subset_1(X73,u1_struct_0(X72))
        | ~ m1_subset_1(X74,u1_struct_0(X72)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_65,negated_conjecture,
    ( v5_waybel_7(esk2_0,esk1_0)
    | r2_hidden(k7_yellow_3(esk1_0,esk1_0,k12_lattice3(esk1_0,X1,X2),k12_lattice3(esk1_0,X3,X4)),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk1_0))
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,X3),esk2_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X2,X4),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_66,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_58])).

cnf(c_0_67,plain,
    ( r3_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r1_orders_2(esk1_0,esk6_0,esk6_0)
    | ~ r1_orders_2(esk1_0,esk5_0,esk5_0)
    | ~ v5_waybel_7(esk2_0,esk1_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_18]),c_0_19]),c_0_20])]),c_0_42]),c_0_34])).

cnf(c_0_70,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,k11_lattice3(esk1_0,X1,X2),k12_lattice3(esk1_0,X3,X4)),esk2_0)
    | v5_waybel_7(esk2_0,esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X2,X4),esk2_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,X3),esk2_0)
    | ~ m1_subset_1(X4,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_72,plain,
    ( k11_lattice3(X1,X2,X2) = X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r1_orders_2(esk1_0,esk6_0,esk6_0)
    | ~ r1_orders_2(esk1_0,esk5_0,esk5_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_18]),c_0_19]),c_0_20])]),c_0_42]),c_0_34])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,k12_lattice3(esk1_0,X2,X3)),esk2_0)
    | v5_waybel_7(esk2_0,esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,X3),esk2_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_18]),c_0_19]),c_0_20]),c_0_73])])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk11_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_7(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,plain,
    ( m1_subset_1(esk12_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_7(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_79,plain,
    ( m1_subset_1(esk13_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_7(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r1_orders_2(esk1_0,esk5_0,esk5_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_18]),c_0_73])]),c_0_22])).

cnf(c_0_81,plain,
    ( v5_waybel_7(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_yellow_3(X1,X1,esk11_2(X1,X2),k11_lattice3(X1,esk12_2(X1,X2),esk13_2(X1,X2))),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,k11_lattice3(esk1_0,X2,X3)),esk2_0)
    | v5_waybel_7(esk2_0,esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,X3),esk2_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v5_waybel_7(esk2_0,esk1_0)
    | m1_subset_1(esk11_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_26]),c_0_18])])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v5_waybel_7(esk2_0,esk1_0)
    | m1_subset_1(esk12_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_26]),c_0_18])])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | v5_waybel_7(esk2_0,esk1_0)
    | m1_subset_1(esk13_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_26]),c_0_18])])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ v5_waybel_7(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_75]),c_0_18]),c_0_73])]),c_0_21])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk11_2(esk1_0,esk2_0),esk13_2(esk1_0,esk2_0)),esk2_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk11_2(esk1_0,esk2_0),esk12_2(esk1_0,esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_26]),c_0_18])]),c_0_83]),c_0_84]),c_0_85]),c_0_86])).

cnf(c_0_88,plain,
    ( r2_hidden(k7_yellow_3(X1,X1,esk11_2(X1,X2),esk13_2(X1,X2)),X2)
    | v5_waybel_7(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ r2_hidden(k7_yellow_3(esk1_0,esk1_0,esk11_2(esk1_0,esk2_0),esk12_2(esk1_0,esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_26]),c_0_18])]),c_0_86])).

cnf(c_0_90,plain,
    ( r2_hidden(k7_yellow_3(X1,X1,esk11_2(X1,X2),esk12_2(X1,X2)),X2)
    | v5_waybel_7(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_26]),c_0_18])]),c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_91]),c_0_18]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
