%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 421 expanded)
%              Number of clauses        :   61 ( 173 expanded)
%              Number of leaves         :   14 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  356 (2779 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_subset_1(X2,u1_struct_0(X1))
            <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_7])).

fof(c_0_15,plain,(
    ! [X33,X34,X35,X36] :
      ( ( ~ v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ r2_hidden(X35,X34)
        | ~ r1_orders_2(X33,X35,X36)
        | r2_hidden(X36,X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_orders_2(X33) )
      & ( m1_subset_1(esk3_2(X33,X34),u1_struct_0(X33))
        | v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_orders_2(X33) )
      & ( m1_subset_1(esk4_2(X33,X34),u1_struct_0(X33))
        | v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(esk3_2(X33,X34),X34)
        | v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_orders_2(X33) )
      & ( r1_orders_2(X33,esk3_2(X33,X34),esk4_2(X33,X34))
        | v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_orders_2(X33) )
      & ( ~ r2_hidden(esk4_2(X33,X34),X34)
        | v13_waybel_0(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,plain,(
    ! [X39,X40] :
      ( ( ~ v1_subset_1(X40,X39)
        | X40 != X39
        | ~ m1_subset_1(X40,k1_zfmisc_1(X39)) )
      & ( X40 = X39
        | v1_subset_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_yellow_0(esk5_0)
    & l1_orders_2(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v2_waybel_0(esk6_0,esk5_0)
    & v13_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      | r2_hidden(k3_yellow_0(esk5_0),esk6_0) )
    & ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_lattice3(X23,X24,X25)
        | X25 != k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_lattice3(X23,X24,X26)
        | r1_orders_2(X23,X25,X26)
        | X25 != k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X23))
        | ~ r2_lattice3(X23,X24,X25)
        | X25 = k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( r2_lattice3(X23,X24,esk2_3(X23,X24,X25))
        | ~ r2_lattice3(X23,X24,X25)
        | X25 = k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,X25,esk2_3(X23,X24,X25))
        | ~ r2_lattice3(X23,X24,X25)
        | X25 = k1_yellow_0(X23,X24)
        | ~ r1_yellow_0(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_20,plain,(
    ! [X28,X29] :
      ( ~ l1_orders_2(X28)
      | m1_subset_1(k1_yellow_0(X28,X29),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_21,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X31,X32] :
      ( ( r2_lattice3(X31,k1_xboole_0,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( r1_lattice3(X31,k1_xboole_0,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_28,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk5_0),esk6_0)
    | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | k3_yellow_0(X22) = k1_yellow_0(X22,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])).

cnf(c_0_35,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X30] :
      ( ( r1_yellow_0(X30,k1_xboole_0)
        | v2_struct_0(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_yellow_0(X30)
        | ~ l1_orders_2(X30) )
      & ( r2_yellow_0(X30,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_yellow_0(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ v13_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X4,k1_yellow_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_45,plain,
    ( r2_lattice3(X1,k1_xboole_0,k1_yellow_0(X1,X2))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)
    | ~ r1_orders_2(esk5_0,X2,k1_yellow_0(esk5_0,X1))
    | ~ r2_hidden(X2,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_40]),c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41])])).

cnf(c_0_53,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,k1_xboole_0),k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r1_yellow_0(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_41])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(u1_struct_0(X1),X2),X3)
    | r1_tarski(u1_struct_0(X1),X2)
    | ~ v13_waybel_0(X3,X1)
    | ~ r1_orders_2(X1,X4,esk1_2(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)
    | ~ r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41])])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),esk1_2(u1_struct_0(X1),X3))
    | r1_tarski(u1_struct_0(X1),X3)
    | ~ r2_lattice3(X1,X2,esk1_2(u1_struct_0(X1),X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_59,plain,
    ( r2_lattice3(X1,k1_xboole_0,esk1_2(u1_struct_0(X1),X2))
    | r1_tarski(u1_struct_0(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_50])).

fof(c_0_60,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_61,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk5_0),X1),esk6_0)
    | r1_tarski(u1_struct_0(esk5_0),X1)
    | ~ r1_orders_2(esk5_0,X2,esk1_2(u1_struct_0(esk5_0),X1))
    | ~ r2_hidden(X2,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_24]),c_0_40]),c_0_41])])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_64,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,k1_xboole_0),esk1_2(u1_struct_0(X1),X2))
    | r1_tarski(u1_struct_0(X1),X2)
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(esk1_2(u1_struct_0(esk5_0),X1),esk6_0)
    | r1_tarski(u1_struct_0(esk5_0),X1)
    | ~ r1_orders_2(esk5_0,k1_yellow_0(esk5_0,X2),esk1_2(u1_struct_0(esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),esk1_2(u1_struct_0(esk5_0),X1))
    | r1_tarski(u1_struct_0(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_54]),c_0_41])])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_24])).

cnf(c_0_71,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_66])).

fof(c_0_74,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_75,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(esk1_2(u1_struct_0(esk5_0),X1),esk6_0)
    | r1_tarski(u1_struct_0(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r1_tarski(u1_struct_0(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_43]),c_0_41])])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_84,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_85,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_83]),c_0_41])]),c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.41  # and selection function SelectNewComplexAHPNS.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.19/0.41  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.19/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.41  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.41  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.19/0.41  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.41  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.19/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.41  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.41  fof(c_0_14, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.19/0.41  fof(c_0_15, plain, ![X33, X34, X35, X36]:((~v13_waybel_0(X34,X33)|(~m1_subset_1(X35,u1_struct_0(X33))|(~m1_subset_1(X36,u1_struct_0(X33))|(~r2_hidden(X35,X34)|~r1_orders_2(X33,X35,X36)|r2_hidden(X36,X34))))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_orders_2(X33))&((m1_subset_1(esk3_2(X33,X34),u1_struct_0(X33))|v13_waybel_0(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_orders_2(X33))&((m1_subset_1(esk4_2(X33,X34),u1_struct_0(X33))|v13_waybel_0(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_orders_2(X33))&(((r2_hidden(esk3_2(X33,X34),X34)|v13_waybel_0(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_orders_2(X33))&(r1_orders_2(X33,esk3_2(X33,X34),esk4_2(X33,X34))|v13_waybel_0(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_orders_2(X33)))&(~r2_hidden(esk4_2(X33,X34),X34)|v13_waybel_0(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_orders_2(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.19/0.41  fof(c_0_16, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.41  fof(c_0_17, plain, ![X39, X40]:((~v1_subset_1(X40,X39)|X40!=X39|~m1_subset_1(X40,k1_zfmisc_1(X39)))&(X40=X39|v1_subset_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.41  fof(c_0_18, negated_conjecture, ((((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v1_yellow_0(esk5_0))&l1_orders_2(esk5_0))&((((~v1_xboole_0(esk6_0)&v2_waybel_0(esk6_0,esk5_0))&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v1_subset_1(esk6_0,u1_struct_0(esk5_0))|r2_hidden(k3_yellow_0(esk5_0),esk6_0))&(v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.41  fof(c_0_19, plain, ![X23, X24, X25, X26]:(((r2_lattice3(X23,X24,X25)|X25!=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_lattice3(X23,X24,X26)|r1_orders_2(X23,X25,X26))|X25!=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23)))&((m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X23))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&((r2_lattice3(X23,X24,esk2_3(X23,X24,X25))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))&(~r1_orders_2(X23,X25,esk2_3(X23,X24,X25))|~r2_lattice3(X23,X24,X25)|X25=k1_yellow_0(X23,X24)|~r1_yellow_0(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|~l1_orders_2(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.19/0.41  fof(c_0_20, plain, ![X28, X29]:(~l1_orders_2(X28)|m1_subset_1(k1_yellow_0(X28,X29),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.41  cnf(c_0_21, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_22, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_25, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_26, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_27, plain, ![X31, X32]:((r2_lattice3(X31,k1_xboole_0,X32)|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))&(r1_lattice3(X31,k1_xboole_0,X32)|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.19/0.41  fof(c_0_28, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.41  fof(c_0_29, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(k3_yellow_0(esk5_0),esk6_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.41  fof(c_0_33, plain, ![X22]:(~l1_orders_2(X22)|k3_yellow_0(X22)=k1_yellow_0(X22,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.41  cnf(c_0_34, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  fof(c_0_36, plain, ![X30]:((r1_yellow_0(X30,k1_xboole_0)|(v2_struct_0(X30)|~v5_orders_2(X30)|~v1_yellow_0(X30)|~l1_orders_2(X30)))&(r2_yellow_0(X30,u1_struct_0(X30))|(v2_struct_0(X30)|~v5_orders_2(X30)|~v1_yellow_0(X30)|~l1_orders_2(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.19/0.41  cnf(c_0_37, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_39, plain, (r2_hidden(k1_yellow_0(X1,X2),X3)|~v13_waybel_0(X3,X1)|~r1_orders_2(X1,X4,k1_yellow_0(X1,X2))|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_43, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.19/0.41  cnf(c_0_45, plain, (r2_lattice3(X1,k1_xboole_0,k1_yellow_0(X1,X2))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_47, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (v1_yellow_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_50, plain, (m1_subset_1(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)|~r1_orders_2(esk5_0,X2,k1_yellow_0(esk5_0,X1))|~r2_hidden(X2,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_24]), c_0_40]), c_0_41])])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41])])).
% 0.19/0.41  cnf(c_0_53, plain, (r1_orders_2(X1,k1_yellow_0(X1,k1_xboole_0),k1_yellow_0(X1,X2))|~r1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r1_yellow_0(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_41])])).
% 0.19/0.41  cnf(c_0_55, plain, (r2_hidden(esk1_2(u1_struct_0(X1),X2),X3)|r1_tarski(u1_struct_0(X1),X2)|~v13_waybel_0(X3,X1)|~r1_orders_2(X1,X4,esk1_2(u1_struct_0(X1),X2))|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_30, c_0_50])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)|~r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),k1_yellow_0(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_41])])).
% 0.19/0.41  cnf(c_0_58, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),esk1_2(u1_struct_0(X1),X3))|r1_tarski(u1_struct_0(X1),X3)|~r2_lattice3(X1,X2,esk1_2(u1_struct_0(X1),X3))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.19/0.41  cnf(c_0_59, plain, (r2_lattice3(X1,k1_xboole_0,esk1_2(u1_struct_0(X1),X2))|r1_tarski(u1_struct_0(X1),X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_50])).
% 0.19/0.41  fof(c_0_60, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  fof(c_0_61, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk5_0),X1),esk6_0)|r1_tarski(u1_struct_0(esk5_0),X1)|~r1_orders_2(esk5_0,X2,esk1_2(u1_struct_0(esk5_0),X1))|~r2_hidden(X2,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_24]), c_0_40]), c_0_41])])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.19/0.41  cnf(c_0_64, plain, (r1_orders_2(X1,k1_yellow_0(X1,k1_xboole_0),esk1_2(u1_struct_0(X1),X2))|r1_tarski(u1_struct_0(X1),X2)|~r1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.41  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.41  cnf(c_0_66, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(esk1_2(u1_struct_0(esk5_0),X1),esk6_0)|r1_tarski(u1_struct_0(esk5_0),X1)|~r1_orders_2(esk5_0,k1_yellow_0(esk5_0,X2),esk1_2(u1_struct_0(esk5_0),X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk5_0,k1_yellow_0(esk5_0,k1_xboole_0),esk1_2(u1_struct_0(esk5_0),X1))|r1_tarski(u1_struct_0(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_54]), c_0_41])])).
% 0.19/0.41  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_24])).
% 0.19/0.41  cnf(c_0_71, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.41  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_66])).
% 0.19/0.41  fof(c_0_74, plain, ![X15, X16]:(~m1_subset_1(X15,X16)|(v1_xboole_0(X16)|r2_hidden(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(esk1_2(u1_struct_0(esk5_0),X1),esk6_0)|r1_tarski(u1_struct_0(esk5_0),X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r1_tarski(u1_struct_0(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.41  cnf(c_0_79, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_71])).
% 0.19/0.41  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.41  cnf(c_0_81, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_43]), c_0_41])])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.19/0.41  cnf(c_0_84, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.19/0.41  cnf(c_0_85, plain, (v1_xboole_0(u1_struct_0(X1))|r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_81, c_0_26])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (~r2_hidden(k1_yellow_0(esk5_0,k1_xboole_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (r2_hidden(k1_yellow_0(esk5_0,X1),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_83]), c_0_41])]), c_0_86])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 90
% 0.19/0.41  # Proof object clause steps            : 61
% 0.19/0.41  # Proof object formula steps           : 29
% 0.19/0.41  # Proof object conjectures             : 31
% 0.19/0.41  # Proof object clause conjectures      : 28
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 26
% 0.19/0.41  # Proof object initial formulas used   : 14
% 0.19/0.41  # Proof object generating inferences   : 27
% 0.19/0.41  # Proof object simplifying inferences  : 35
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 14
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 42
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 42
% 0.19/0.41  # Processed clauses                    : 404
% 0.19/0.41  # ...of these trivial                  : 2
% 0.19/0.41  # ...subsumed                          : 96
% 0.19/0.41  # ...remaining for further processing  : 306
% 0.19/0.41  # Other redundant clauses eliminated   : 5
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 51
% 0.19/0.41  # Backward-rewritten                   : 110
% 0.19/0.41  # Generated clauses                    : 542
% 0.19/0.41  # ...of the previous two non-trivial   : 542
% 0.19/0.41  # Contextual simplify-reflections      : 17
% 0.19/0.41  # Paramodulations                      : 537
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 5
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 140
% 0.19/0.41  #    Positive orientable unit clauses  : 16
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 4
% 0.19/0.41  #    Non-unit-clauses                  : 120
% 0.19/0.41  # Current number of unprocessed clauses: 164
% 0.19/0.41  # ...number of literals in the above   : 793
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 161
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 7457
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1156
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 160
% 0.19/0.41  # Unit Clause-clause subsumption calls : 202
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 35
% 0.19/0.41  # BW rewrite match successes           : 9
% 0.19/0.41  # Condensation attempts                : 405
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 20245
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.070 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.075 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
