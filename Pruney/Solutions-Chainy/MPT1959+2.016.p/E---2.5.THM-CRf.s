%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:25 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 524 expanded)
%              Number of clauses        :   64 ( 221 expanded)
%              Number of leaves         :   17 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  398 (3205 expanded)
%              Number of equality atoms :   49 ( 188 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

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

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X23,X22)
        | r2_hidden(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ r2_hidden(X23,X22)
        | m1_subset_1(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ m1_subset_1(X23,X22)
        | v1_xboole_0(X23)
        | ~ v1_xboole_0(X22) )
      & ( ~ v1_xboole_0(X23)
        | m1_subset_1(X23,X22)
        | ~ v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v3_orders_2(esk9_0)
    & v4_orders_2(esk9_0)
    & v5_orders_2(esk9_0)
    & v1_yellow_0(esk9_0)
    & l1_orders_2(esk9_0)
    & ~ v1_xboole_0(esk10_0)
    & v2_waybel_0(esk10_0,esk9_0)
    & v13_waybel_0(esk10_0,esk9_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))
    & ( ~ v1_subset_1(esk10_0,u1_struct_0(esk9_0))
      | r2_hidden(k3_yellow_0(esk9_0),esk10_0) )
    & ( v1_subset_1(esk10_0,u1_struct_0(esk9_0))
      | ~ r2_hidden(k3_yellow_0(esk9_0),esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X15)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r1_tarski(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r1_tarski(esk3_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | r1_tarski(esk3_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_26,plain,(
    ! [X25] : m1_subset_1(k2_subset_1(X25),k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_27,plain,(
    ! [X24] : k2_subset_1(X24) = X24 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ( m1_subset_1(esk4_3(X26,X27,X28),X26)
        | X27 = X28
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( ~ r2_hidden(esk4_3(X26,X27,X28),X27)
        | ~ r2_hidden(esk4_3(X26,X27,X28),X28)
        | X27 = X28
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( r2_hidden(esk4_3(X26,X27,X28),X27)
        | r2_hidden(esk4_3(X26,X27,X28),X28)
        | X27 = X28
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | k1_zfmisc_1(u1_struct_0(esk9_0)) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk10_0,u1_struct_0(esk9_0)) ),
    inference(er,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_40,plain,(
    ! [X44,X45] :
      ( ~ l1_orders_2(X44)
      | m1_subset_1(k1_yellow_0(X44,X45),u1_struct_0(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_41,plain,(
    ! [X33,X34,X35,X36] :
      ( ( ~ r2_lattice3(X33,X34,X35)
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ r2_hidden(X36,X34)
        | r1_orders_2(X33,X36,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ l1_orders_2(X33) )
      & ( m1_subset_1(esk5_3(X33,X34,X35),u1_struct_0(X33))
        | r2_lattice3(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(esk5_3(X33,X34,X35),X34)
        | r2_lattice3(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ l1_orders_2(X33) )
      & ( ~ r1_orders_2(X33,esk5_3(X33,X34,X35),X35)
        | r2_lattice3(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_42,plain,
    ( X1 = X2
    | m1_subset_1(esk4_3(X2,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_lattice3(X39,X40,X41)
        | X41 != k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r2_lattice3(X39,X40,X42)
        | r1_orders_2(X39,X41,X42)
        | X41 != k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( m1_subset_1(esk6_3(X39,X40,X41),u1_struct_0(X39))
        | ~ r2_lattice3(X39,X40,X41)
        | X41 = k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( r2_lattice3(X39,X40,esk6_3(X39,X40,X41))
        | ~ r2_lattice3(X39,X40,X41)
        | X41 = k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( ~ r1_orders_2(X39,X41,esk6_3(X39,X40,X41))
        | ~ r2_lattice3(X39,X40,X41)
        | X41 = k1_yellow_0(X39,X40)
        | ~ r1_yellow_0(X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ l1_orders_2(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | m1_subset_1(esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21])).

fof(c_0_50,plain,(
    ! [X47,X48,X49,X50] :
      ( ( ~ v13_waybel_0(X48,X47)
        | ~ m1_subset_1(X49,u1_struct_0(X47))
        | ~ m1_subset_1(X50,u1_struct_0(X47))
        | ~ r2_hidden(X49,X48)
        | ~ r1_orders_2(X47,X49,X50)
        | r2_hidden(X50,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_orders_2(X47) )
      & ( m1_subset_1(esk7_2(X47,X48),u1_struct_0(X47))
        | v13_waybel_0(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_orders_2(X47) )
      & ( m1_subset_1(esk8_2(X47,X48),u1_struct_0(X47))
        | v13_waybel_0(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_orders_2(X47) )
      & ( r2_hidden(esk7_2(X47,X48),X48)
        | v13_waybel_0(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_orders_2(X47) )
      & ( r1_orders_2(X47,esk7_2(X47,X48),esk8_2(X47,X48))
        | v13_waybel_0(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_orders_2(X47) )
      & ( ~ r2_hidden(esk8_2(X47,X48),X48)
        | v13_waybel_0(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ l1_orders_2(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_51,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_1(esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_22])).

cnf(c_0_54,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r2_lattice3(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))
    | r2_hidden(esk5_3(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_47])])).

fof(c_0_57,plain,(
    ! [X46] :
      ( ( r1_yellow_0(X46,k1_xboole_0)
        | v2_struct_0(X46)
        | ~ v5_orders_2(X46)
        | ~ v1_yellow_0(X46)
        | ~ l1_orders_2(X46) )
      & ( r2_yellow_0(X46,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v5_orders_2(X46)
        | ~ v1_yellow_0(X46)
        | ~ l1_orders_2(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_58,plain,(
    ! [X38] :
      ( ~ l1_orders_2(X38)
      | k3_yellow_0(X38) = k1_yellow_0(X38,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_59,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_yellow_0(esk9_0,X1),X2)
    | k1_yellow_0(esk9_0,X1) != k1_yellow_0(esk9_0,X3)
    | ~ r1_yellow_0(esk9_0,X3)
    | ~ r2_lattice3(esk9_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r2_lattice3(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_64,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_65,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( v1_yellow_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( v5_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_70,plain,(
    ! [X53,X54] :
      ( ( ~ v1_subset_1(X54,X53)
        | X54 != X53
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53)) )
      & ( X54 = X53
        | v1_subset_1(X54,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( v13_waybel_0(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_73,plain,
    ( X2 = X3
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r2_hidden(esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_49]),c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r1_orders_2(esk9_0,k1_yellow_0(esk9_0,X1),esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))
    | k1_yellow_0(esk9_0,X1) != k1_yellow_0(esk9_0,X2)
    | ~ r1_yellow_0(esk9_0,X2)
    | ~ r2_lattice3(esk9_0,X2,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_49])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r2_lattice3(esk9_0,k1_xboole_0,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r1_yellow_0(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_47])]),c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk9_0),esk10_0)
    | ~ v1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( k3_yellow_0(esk9_0) = k1_yellow_0(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_47])).

cnf(c_0_80,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r1_orders_2(esk9_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X2,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_21]),c_0_72]),c_0_47])])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | ~ r2_hidden(esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_36]),c_0_21])])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r1_orders_2(esk9_0,k1_yellow_0(esk9_0,X1),esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))
    | k1_yellow_0(esk9_0,X1) != k1_yellow_0(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0)
    | ~ v1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | v1_subset_1(esk10_0,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( v1_subset_1(esk10_0,u1_struct_0(esk9_0))
    | ~ r2_hidden(k3_yellow_0(esk9_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | ~ r1_orders_2(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_49]),c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r1_orders_2(esk9_0,k1_yellow_0(esk9_0,k1_xboole_0),esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0))) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0
    | r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_91,negated_conjecture,
    ( v1_subset_1(esk10_0,u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk9_0) = esk10_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_93,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_90]),c_0_36])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_55]),c_0_61])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk9_0,X1),esk10_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:44:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.37/1.53  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0S
% 1.37/1.53  # and selection function SelectComplexG.
% 1.37/1.53  #
% 1.37/1.53  # Preprocessing time       : 0.030 s
% 1.37/1.53  # Presaturation interreduction done
% 1.37/1.53  
% 1.37/1.53  # Proof found!
% 1.37/1.53  # SZS status Theorem
% 1.37/1.53  # SZS output start CNFRefutation
% 1.37/1.53  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 1.37/1.53  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.37/1.53  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.37/1.53  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.37/1.53  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.37/1.53  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 1.37/1.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.37/1.53  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.37/1.53  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 1.37/1.53  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.37/1.53  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 1.37/1.53  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 1.37/1.53  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.37/1.53  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 1.37/1.53  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 1.37/1.53  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.37/1.53  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 1.37/1.53  fof(c_0_17, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 1.37/1.53  fof(c_0_18, plain, ![X22, X23]:(((~m1_subset_1(X23,X22)|r2_hidden(X23,X22)|v1_xboole_0(X22))&(~r2_hidden(X23,X22)|m1_subset_1(X23,X22)|v1_xboole_0(X22)))&((~m1_subset_1(X23,X22)|v1_xboole_0(X23)|~v1_xboole_0(X22))&(~v1_xboole_0(X23)|m1_subset_1(X23,X22)|~v1_xboole_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.37/1.53  fof(c_0_19, negated_conjecture, ((((((~v2_struct_0(esk9_0)&v3_orders_2(esk9_0))&v4_orders_2(esk9_0))&v5_orders_2(esk9_0))&v1_yellow_0(esk9_0))&l1_orders_2(esk9_0))&((((~v1_xboole_0(esk10_0)&v2_waybel_0(esk10_0,esk9_0))&v13_waybel_0(esk10_0,esk9_0))&m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0))))&((~v1_subset_1(esk10_0,u1_struct_0(esk9_0))|r2_hidden(k3_yellow_0(esk9_0),esk10_0))&(v1_subset_1(esk10_0,u1_struct_0(esk9_0))|~r2_hidden(k3_yellow_0(esk9_0),esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 1.37/1.53  cnf(c_0_20, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.37/1.53  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  fof(c_0_23, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|r1_tarski(X17,X15)|X16!=k1_zfmisc_1(X15))&(~r1_tarski(X18,X15)|r2_hidden(X18,X16)|X16!=k1_zfmisc_1(X15)))&((~r2_hidden(esk3_2(X19,X20),X20)|~r1_tarski(esk3_2(X19,X20),X19)|X20=k1_zfmisc_1(X19))&(r2_hidden(esk3_2(X19,X20),X20)|r1_tarski(esk3_2(X19,X20),X19)|X20=k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.37/1.53  cnf(c_0_24, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.37/1.53  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 1.37/1.53  fof(c_0_26, plain, ![X25]:m1_subset_1(k2_subset_1(X25),k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 1.37/1.53  fof(c_0_27, plain, ![X24]:k2_subset_1(X24)=X24, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 1.37/1.53  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.37/1.53  cnf(c_0_29, negated_conjecture, (r2_hidden(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_25])).
% 1.37/1.53  fof(c_0_30, plain, ![X26, X27, X28]:((m1_subset_1(esk4_3(X26,X27,X28),X26)|X27=X28|~m1_subset_1(X28,k1_zfmisc_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(X26)))&((~r2_hidden(esk4_3(X26,X27,X28),X27)|~r2_hidden(esk4_3(X26,X27,X28),X28)|X27=X28|~m1_subset_1(X28,k1_zfmisc_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(X26)))&(r2_hidden(esk4_3(X26,X27,X28),X27)|r2_hidden(esk4_3(X26,X27,X28),X28)|X27=X28|~m1_subset_1(X28,k1_zfmisc_1(X26))|~m1_subset_1(X27,k1_zfmisc_1(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 1.37/1.53  cnf(c_0_31, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.37/1.53  cnf(c_0_32, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.37/1.53  fof(c_0_33, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.37/1.53  cnf(c_0_34, negated_conjecture, (r1_tarski(esk10_0,X1)|k1_zfmisc_1(u1_struct_0(esk9_0))!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.37/1.53  cnf(c_0_35, plain, (m1_subset_1(esk4_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.37/1.53  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 1.37/1.53  cnf(c_0_37, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.37/1.53  cnf(c_0_38, negated_conjecture, (r1_tarski(esk10_0,u1_struct_0(esk9_0))), inference(er,[status(thm)],[c_0_34])).
% 1.37/1.53  fof(c_0_39, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.37/1.53  fof(c_0_40, plain, ![X44, X45]:(~l1_orders_2(X44)|m1_subset_1(k1_yellow_0(X44,X45),u1_struct_0(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 1.37/1.53  fof(c_0_41, plain, ![X33, X34, X35, X36]:((~r2_lattice3(X33,X34,X35)|(~m1_subset_1(X36,u1_struct_0(X33))|(~r2_hidden(X36,X34)|r1_orders_2(X33,X36,X35)))|~m1_subset_1(X35,u1_struct_0(X33))|~l1_orders_2(X33))&((m1_subset_1(esk5_3(X33,X34,X35),u1_struct_0(X33))|r2_lattice3(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|~l1_orders_2(X33))&((r2_hidden(esk5_3(X33,X34,X35),X34)|r2_lattice3(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|~l1_orders_2(X33))&(~r1_orders_2(X33,esk5_3(X33,X34,X35),X35)|r2_lattice3(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|~l1_orders_2(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 1.37/1.53  cnf(c_0_42, plain, (X1=X2|m1_subset_1(esk4_3(X2,X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.37/1.53  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk9_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.37/1.53  cnf(c_0_44, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.37/1.53  fof(c_0_45, plain, ![X39, X40, X41, X42]:(((r2_lattice3(X39,X40,X41)|X41!=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r2_lattice3(X39,X40,X42)|r1_orders_2(X39,X41,X42))|X41!=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39)))&((m1_subset_1(esk6_3(X39,X40,X41),u1_struct_0(X39))|~r2_lattice3(X39,X40,X41)|X41=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))&((r2_lattice3(X39,X40,esk6_3(X39,X40,X41))|~r2_lattice3(X39,X40,X41)|X41=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))&(~r1_orders_2(X39,X41,esk6_3(X39,X40,X41))|~r2_lattice3(X39,X40,X41)|X41=k1_yellow_0(X39,X40)|~r1_yellow_0(X39,X40)|~m1_subset_1(X41,u1_struct_0(X39))|~l1_orders_2(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 1.37/1.53  cnf(c_0_46, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.37/1.53  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_48, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.37/1.53  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|m1_subset_1(esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_42, c_0_21])).
% 1.37/1.53  fof(c_0_50, plain, ![X47, X48, X49, X50]:((~v13_waybel_0(X48,X47)|(~m1_subset_1(X49,u1_struct_0(X47))|(~m1_subset_1(X50,u1_struct_0(X47))|(~r2_hidden(X49,X48)|~r1_orders_2(X47,X49,X50)|r2_hidden(X50,X48))))|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_orders_2(X47))&((m1_subset_1(esk7_2(X47,X48),u1_struct_0(X47))|v13_waybel_0(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_orders_2(X47))&((m1_subset_1(esk8_2(X47,X48),u1_struct_0(X47))|v13_waybel_0(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_orders_2(X47))&(((r2_hidden(esk7_2(X47,X48),X48)|v13_waybel_0(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_orders_2(X47))&(r1_orders_2(X47,esk7_2(X47,X48),esk8_2(X47,X48))|v13_waybel_0(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_orders_2(X47)))&(~r2_hidden(esk8_2(X47,X48),X48)|v13_waybel_0(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~l1_orders_2(X47)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 1.37/1.53  fof(c_0_51, plain, ![X30, X31, X32]:(~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(X32))|m1_subset_1(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.37/1.53  cnf(c_0_52, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.37/1.53  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_1(esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_22])).
% 1.37/1.53  cnf(c_0_54, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.37/1.53  cnf(c_0_55, negated_conjecture, (m1_subset_1(k1_yellow_0(esk9_0,X1),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.37/1.53  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r2_lattice3(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))|r2_hidden(esk5_3(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_47])])).
% 1.37/1.53  fof(c_0_57, plain, ![X46]:((r1_yellow_0(X46,k1_xboole_0)|(v2_struct_0(X46)|~v5_orders_2(X46)|~v1_yellow_0(X46)|~l1_orders_2(X46)))&(r2_yellow_0(X46,u1_struct_0(X46))|(v2_struct_0(X46)|~v5_orders_2(X46)|~v1_yellow_0(X46)|~l1_orders_2(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 1.37/1.53  fof(c_0_58, plain, ![X38]:(~l1_orders_2(X38)|k3_yellow_0(X38)=k1_yellow_0(X38,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 1.37/1.53  cnf(c_0_59, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.37/1.53  cnf(c_0_60, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.37/1.53  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.37/1.53  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk9_0,k1_yellow_0(esk9_0,X1),X2)|k1_yellow_0(esk9_0,X1)!=k1_yellow_0(esk9_0,X3)|~r1_yellow_0(esk9_0,X3)|~r2_lattice3(esk9_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_47])])).
% 1.37/1.53  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r2_lattice3(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 1.37/1.53  cnf(c_0_64, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.37/1.53  cnf(c_0_65, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.37/1.53  cnf(c_0_66, negated_conjecture, (v1_yellow_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_67, negated_conjecture, (v5_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_69, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.37/1.53  fof(c_0_70, plain, ![X53, X54]:((~v1_subset_1(X54,X53)|X54!=X53|~m1_subset_1(X54,k1_zfmisc_1(X53)))&(X54=X53|v1_subset_1(X54,X53)|~m1_subset_1(X54,k1_zfmisc_1(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 1.37/1.53  cnf(c_0_71, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_59, c_0_60])).
% 1.37/1.53  cnf(c_0_72, negated_conjecture, (v13_waybel_0(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_73, plain, (X2=X3|~r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(esk4_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.37/1.53  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r2_hidden(esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_49]), c_0_61])).
% 1.37/1.53  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r1_orders_2(esk9_0,k1_yellow_0(esk9_0,X1),esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))|k1_yellow_0(esk9_0,X1)!=k1_yellow_0(esk9_0,X2)|~r1_yellow_0(esk9_0,X2)|~r2_lattice3(esk9_0,X2,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))), inference(spm,[status(thm)],[c_0_62, c_0_49])).
% 1.37/1.53  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r2_lattice3(esk9_0,k1_xboole_0,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 1.37/1.53  cnf(c_0_77, negated_conjecture, (r1_yellow_0(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_47])]), c_0_68])).
% 1.37/1.53  cnf(c_0_78, negated_conjecture, (r2_hidden(k3_yellow_0(esk9_0),esk10_0)|~v1_subset_1(esk10_0,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_79, negated_conjecture, (k3_yellow_0(esk9_0)=k1_yellow_0(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_47])).
% 1.37/1.53  cnf(c_0_80, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.37/1.53  cnf(c_0_81, negated_conjecture, (r2_hidden(X1,esk10_0)|~r1_orders_2(esk9_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~r2_hidden(X2,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_21]), c_0_72]), c_0_47])])).
% 1.37/1.53  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|~r2_hidden(esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_36]), c_0_21])])).
% 1.37/1.53  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r1_orders_2(esk9_0,k1_yellow_0(esk9_0,X1),esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))|k1_yellow_0(esk9_0,X1)!=k1_yellow_0(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])])).
% 1.37/1.53  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0)|~v1_subset_1(esk10_0,u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 1.37/1.53  cnf(c_0_85, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|v1_subset_1(esk10_0,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_80, c_0_21])).
% 1.37/1.53  cnf(c_0_86, negated_conjecture, (v1_subset_1(esk10_0,u1_struct_0(esk9_0))|~r2_hidden(k3_yellow_0(esk9_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.37/1.53  cnf(c_0_87, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|~r1_orders_2(esk9_0,X1,esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))|~r2_hidden(X1,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_49]), c_0_82])).
% 1.37/1.53  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r1_orders_2(esk9_0,k1_yellow_0(esk9_0,k1_xboole_0),esk4_3(u1_struct_0(esk9_0),esk10_0,u1_struct_0(esk9_0)))), inference(er,[status(thm)],[c_0_83])).
% 1.37/1.53  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0|r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 1.37/1.53  cnf(c_0_90, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.37/1.53  cnf(c_0_91, negated_conjecture, (v1_subset_1(esk10_0,u1_struct_0(esk9_0))|~r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0)), inference(rw,[status(thm)],[c_0_86, c_0_79])).
% 1.37/1.53  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk9_0)=esk10_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 1.37/1.53  cnf(c_0_93, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_90]), c_0_36])])).
% 1.37/1.53  cnf(c_0_94, negated_conjecture, (r2_hidden(k1_yellow_0(esk9_0,X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_55]), c_0_61])).
% 1.37/1.53  cnf(c_0_95, negated_conjecture, (~r2_hidden(k1_yellow_0(esk9_0,k1_xboole_0),esk10_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 1.37/1.53  cnf(c_0_96, negated_conjecture, (r2_hidden(k1_yellow_0(esk9_0,X1),esk10_0)), inference(rw,[status(thm)],[c_0_94, c_0_92])).
% 1.37/1.53  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])]), ['proof']).
% 1.37/1.53  # SZS output end CNFRefutation
% 1.37/1.53  # Proof object total steps             : 98
% 1.37/1.53  # Proof object clause steps            : 64
% 1.37/1.53  # Proof object formula steps           : 34
% 1.37/1.53  # Proof object conjectures             : 43
% 1.37/1.53  # Proof object clause conjectures      : 40
% 1.37/1.53  # Proof object formula conjectures     : 3
% 1.37/1.53  # Proof object initial clauses used    : 29
% 1.37/1.53  # Proof object initial formulas used   : 17
% 1.37/1.53  # Proof object generating inferences   : 27
% 1.37/1.53  # Proof object simplifying inferences  : 35
% 1.37/1.53  # Training examples: 0 positive, 0 negative
% 1.37/1.53  # Parsed axioms                        : 17
% 1.37/1.53  # Removed by relevancy pruning/SinE    : 0
% 1.37/1.53  # Initial clauses                      : 53
% 1.37/1.53  # Removed in clause preprocessing      : 1
% 1.37/1.53  # Initial clauses in saturation        : 52
% 1.37/1.53  # Processed clauses                    : 6898
% 1.37/1.53  # ...of these trivial                  : 13
% 1.37/1.53  # ...subsumed                          : 3715
% 1.37/1.53  # ...remaining for further processing  : 3170
% 1.37/1.53  # Other redundant clauses eliminated   : 1
% 1.37/1.53  # Clauses deleted for lack of memory   : 0
% 1.37/1.53  # Backward-subsumed                    : 212
% 1.37/1.53  # Backward-rewritten                   : 1282
% 1.37/1.53  # Generated clauses                    : 62994
% 1.37/1.53  # ...of the previous two non-trivial   : 61731
% 1.37/1.53  # Contextual simplify-reflections      : 56
% 1.37/1.53  # Paramodulations                      : 62761
% 1.37/1.53  # Factorizations                       : 12
% 1.37/1.53  # Equation resolutions                 : 221
% 1.37/1.53  # Propositional unsat checks           : 0
% 1.37/1.53  #    Propositional check models        : 0
% 1.37/1.53  #    Propositional check unsatisfiable : 0
% 1.37/1.53  #    Propositional clauses             : 0
% 1.37/1.53  #    Propositional clauses after purity: 0
% 1.37/1.53  #    Propositional unsat core size     : 0
% 1.37/1.53  #    Propositional preprocessing time  : 0.000
% 1.37/1.53  #    Propositional encoding time       : 0.000
% 1.37/1.53  #    Propositional solver time         : 0.000
% 1.37/1.53  #    Success case prop preproc time    : 0.000
% 1.37/1.53  #    Success case prop encoding time   : 0.000
% 1.37/1.53  #    Success case prop solver time     : 0.000
% 1.37/1.53  # Current number of processed clauses  : 1623
% 1.37/1.53  #    Positive orientable unit clauses  : 40
% 1.37/1.53  #    Positive unorientable unit clauses: 0
% 1.37/1.53  #    Negative unit clauses             : 4
% 1.37/1.53  #    Non-unit-clauses                  : 1579
% 1.37/1.53  # Current number of unprocessed clauses: 54645
% 1.37/1.53  # ...number of literals in the above   : 247762
% 1.37/1.53  # Current number of archived formulas  : 0
% 1.37/1.53  # Current number of archived clauses   : 1547
% 1.37/1.53  # Clause-clause subsumption calls (NU) : 1452461
% 1.37/1.53  # Rec. Clause-clause subsumption calls : 506246
% 1.37/1.53  # Non-unit clause-clause subsumptions  : 3402
% 1.37/1.53  # Unit Clause-clause subsumption calls : 12912
% 1.37/1.53  # Rewrite failures with RHS unbound    : 0
% 1.37/1.53  # BW rewrite match attempts            : 90
% 1.37/1.53  # BW rewrite match successes           : 17
% 1.37/1.53  # Condensation attempts                : 0
% 1.37/1.53  # Condensation successes               : 0
% 1.37/1.53  # Termbank termtop insertions          : 1961350
% 1.37/1.53  
% 1.37/1.53  # -------------------------------------------------
% 1.37/1.53  # User time                : 1.161 s
% 1.37/1.53  # System time              : 0.037 s
% 1.37/1.53  # Total time               : 1.198 s
% 1.37/1.53  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
