%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1625+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 311 expanded)
%              Number of clauses        :   50 ( 117 expanded)
%              Number of leaves         :   11 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  394 (1773 expanded)
%              Number of equality atoms :   31 (  98 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   55 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1)
            & v2_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_waybel_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(d2_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X5,X3)
                                & r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d1_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X3,X5)
                                & r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1)
              & v2_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_0])).

fof(c_0_12,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v3_orders_2(X38)
      | ~ l1_orders_2(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | r3_orders_2(X38,X39,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v3_orders_2(esk8_0)
    & l1_orders_2(esk8_0)
    & m1_subset_1(esk9_0,u1_struct_0(esk8_0))
    & ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(esk8_0),esk9_0),esk8_0)
      | ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk8_0),esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24,X28] :
      ( ( m1_subset_1(esk5_4(X21,X22,X23,X24),u1_struct_0(X21))
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(esk5_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,esk5_4(X21,X22,X23,X24),X23)
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,esk5_4(X21,X22,X23,X24),X24)
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk6_2(X21,X22),u1_struct_0(X21))
        | v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk7_2(X21,X22),u1_struct_0(X21))
        | v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(esk6_2(X21,X22),X22)
        | v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(esk7_2(X21,X22),X22)
        | v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X21))
        | ~ r2_hidden(X28,X22)
        | ~ r1_orders_2(X21,X28,esk6_2(X21,X22))
        | ~ r1_orders_2(X21,X28,esk7_2(X21,X22))
        | v2_waybel_0(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_waybel_0])])])])])).

fof(c_0_15,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | m1_subset_1(X41,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r3_orders_2(X35,X36,X37)
        | r1_orders_2(X35,X36,X37)
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35)) )
      & ( ~ r1_orders_2(X35,X36,X37)
        | r3_orders_2(X35,X36,X37)
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_23,plain,
    ( v2_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,X1,esk6_2(X2,X3))
    | ~ r1_orders_2(X2,X1,esk7_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_27,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X13,X14,X15,X16,X20] :
      ( ( m1_subset_1(esk2_4(X13,X14,X15,X16),u1_struct_0(X13))
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk2_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r1_orders_2(X13,X15,esk2_4(X13,X14,X15,X16))
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r1_orders_2(X13,X16,esk2_4(X13,X14,X15,X16))
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk3_2(X13,X14),u1_struct_0(X13))
        | v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk4_2(X13,X14),u1_struct_0(X13))
        | v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X14)
        | v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk4_2(X13,X14),X14)
        | v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(X20,X14)
        | ~ r1_orders_2(X13,esk3_2(X13,X14),X20)
        | ~ r1_orders_2(X13,esk4_2(X13,X14),X20)
        | v1_waybel_0(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_waybel_0])])])])])).

cnf(c_0_30,plain,
    ( v2_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,X3,esk6_2(X2,X1))
    | ~ r1_orders_2(X2,X3,esk7_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_32,plain,
    ( esk6_2(X1,X2) = X3
    | v2_waybel_0(X2,X1)
    | X2 != k1_tarski(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,esk3_2(X2,X3),X1)
    | ~ r1_orders_2(X2,esk4_2(X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_38,negated_conjecture,
    ( v2_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,esk7_2(esk8_0,X1),esk6_2(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(esk7_2(esk8_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_20])]),c_0_24])).

cnf(c_0_39,plain,
    ( esk6_2(X1,k1_tarski(X2)) = X2
    | v2_waybel_0(k1_tarski(X2),X1)
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( esk7_2(X1,X2) = X3
    | v2_waybel_0(X2,X1)
    | X2 != k1_tarski(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | ~ m1_subset_1(X30,X29)
      | m1_subset_1(k6_domain_1(X29,X30),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_43,plain,
    ( v1_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,esk3_2(X2,X1),X3)
    | ~ r1_orders_2(X2,esk4_2(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_44,plain,
    ( esk3_2(X1,X2) = X3
    | v1_waybel_0(X2,X1)
    | X2 != k1_tarski(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_waybel_0(k1_tarski(X1),esk8_0)
    | ~ r1_orders_2(esk8_0,esk7_2(esk8_0,k1_tarski(X1)),X1)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(esk7_2(esk8_0,k1_tarski(X1)),k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_20])])).

cnf(c_0_48,plain,
    ( esk7_2(X1,k1_tarski(X2)) = X2
    | v2_waybel_0(k1_tarski(X2),X1)
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_waybel_0(X1,esk8_0)
    | ~ r1_orders_2(esk8_0,esk3_2(esk8_0,X1),esk4_2(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(esk4_2(esk8_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_20])]),c_0_24])).

cnf(c_0_52,plain,
    ( esk3_2(X1,k1_tarski(X2)) = X2
    | v1_waybel_0(k1_tarski(X2),X1)
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( esk4_2(X1,X2) = X3
    | v1_waybel_0(X2,X1)
    | X2 != k1_tarski(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(esk8_0),esk9_0),esk8_0)
    | ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk8_0),esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk8_0),esk9_0) = k1_tarski(esk9_0)
    | v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( v2_waybel_0(k1_tarski(X1),esk8_0)
    | ~ r1_orders_2(esk8_0,X1,X1)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_20])])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk8_0),esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( v1_waybel_0(k1_tarski(X1),esk8_0)
    | ~ r1_orders_2(esk8_0,X1,esk4_2(esk8_0,k1_tarski(X1)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ r2_hidden(esk4_2(esk8_0,k1_tarski(X1)),k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_20])])).

cnf(c_0_59,plain,
    ( esk4_2(X1,k1_tarski(X2)) = X2
    | v1_waybel_0(k1_tarski(X2),X1)
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_61,plain,(
    ! [X31] :
      ( ~ l1_orders_2(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | ~ v2_waybel_0(k1_tarski(esk9_0),esk8_0)
    | ~ v1_waybel_0(k1_tarski(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v2_waybel_0(k1_tarski(X1),esk8_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | m1_subset_1(k1_tarski(esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v1_waybel_0(k1_tarski(X1),esk8_0)
    | ~ r1_orders_2(esk8_0,X1,X1)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49]),c_0_20])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | ~ v1_waybel_0(k1_tarski(esk9_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_18])]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_waybel_0(k1_tarski(X1),esk8_0)
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_31])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_18])]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_20])]),c_0_21]),
    [proof]).

%------------------------------------------------------------------------------
