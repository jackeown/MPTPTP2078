%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:29 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  563 (10986 expanded)
%              Number of clauses        :  514 (5554 expanded)
%              Number of leaves         :   24 (2689 expanded)
%              Depth                    :   10
%              Number of atoms          : 2288 (43777 expanded)
%              Number of equality atoms :  709 (10750 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(t67_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v23_waybel_0(X3,X1,X2)
               => ( v1_funct_1(k2_funct_1(X3))
                  & v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & k2_relat_1(k2_funct_1(X3)) = u1_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_waybel_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(rc4_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ? [X2] :
          ( m1_yellow_0(X2,X1)
          & ~ v2_struct_0(X2)
          & v1_orders_2(X2)
          & v4_yellow_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_yellow_0)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_24,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | ~ r1_tarski(esk1_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(esk1_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_25,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_26,plain,(
    ! [X49,X50,X51] :
      ( ( X50 = k1_xboole_0
        | ~ r2_hidden(X50,X49)
        | k3_tarski(X49) != k1_xboole_0 )
      & ( esk2_1(X51) != k1_xboole_0
        | k3_tarski(X51) = k1_xboole_0 )
      & ( r2_hidden(esk2_1(X51),X51)
        | k3_tarski(X51) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_27,plain,(
    ! [X17] : k3_tarski(k1_zfmisc_1(X17)) = X17 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_tarski(esk1_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_33,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_28]),
    [final]).

fof(c_0_35,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(X9)
      | ~ r1_tarski(X9,X8)
      | ~ r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_36,plain,(
    ! [X7] : r1_xboole_0(X7,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_37,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_39,plain,
    ( X1 = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31]),
    [final]).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31]),
    [final]).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

fof(c_0_44,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))
      | ~ r1_tarski(k2_relat_1(X35),X33)
      | m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_47,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [final]).

fof(c_0_48,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_49,plain,
    ( esk1_2(k1_xboole_0,X1) = k1_xboole_0
    | X1 = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [final]).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_51,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31]),
    [final]).

cnf(c_0_52,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | k3_tarski(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

fof(c_0_53,plain,(
    ! [X41,X42,X43] :
      ( ( X42 = k1_xboole_0
        | v1_partfun1(X43,X41)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X41 != k1_xboole_0
        | v1_partfun1(X43,X41)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_orders_2(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v23_waybel_0(X3,X1,X2)
                 => ( v1_funct_1(k2_funct_1(X3))
                    & v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & k2_relat_1(k2_funct_1(X3)) = u1_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_waybel_0])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_57,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46]),
    [final]).

cnf(c_0_58,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_47]),
    [final]).

cnf(c_0_59,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48]),
    [final]).

cnf(c_0_60,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48]),
    [final]).

cnf(c_0_61,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_49]),
    [final]).

cnf(c_0_62,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))
    | r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51]),
    [final]).

cnf(c_0_63,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51]),
    [final]).

cnf(c_0_64,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51]),
    [final]).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_52]),c_0_33]),
    [final]).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_orders_2(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & l1_orders_2(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v23_waybel_0(esk6_0,esk4_0,esk5_0)
    & ( ~ v1_funct_1(k2_funct_1(esk6_0))
      | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
      | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
      | k2_relat_1(k2_funct_1(esk6_0)) != u1_struct_0(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_54])])])])).

fof(c_0_68,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_69,plain,(
    ! [X19] : m1_subset_1(k1_subset_1(X19),k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_70,plain,(
    ! [X18] : k1_subset_1(X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_71,plain,(
    ! [X53,X54] :
      ( ( r1_tarski(u1_struct_0(X54),u1_struct_0(X53))
        | ~ m1_yellow_0(X54,X53)
        | ~ l1_orders_2(X54)
        | ~ l1_orders_2(X53) )
      & ( r1_tarski(u1_orders_2(X54),u1_orders_2(X53))
        | ~ m1_yellow_0(X54,X53)
        | ~ l1_orders_2(X54)
        | ~ l1_orders_2(X53) )
      & ( ~ r1_tarski(u1_struct_0(X54),u1_struct_0(X53))
        | ~ r1_tarski(u1_orders_2(X54),u1_orders_2(X53))
        | m1_yellow_0(X54,X53)
        | ~ l1_orders_2(X54)
        | ~ l1_orders_2(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_72,plain,(
    ! [X55,X56] :
      ( ~ l1_orders_2(X55)
      | ~ m1_yellow_0(X56,X55)
      | l1_orders_2(X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_74,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [final]).

cnf(c_0_75,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [final]).

cnf(c_0_76,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_58]),
    [final]).

cnf(c_0_77,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_58]),
    [final]).

cnf(c_0_78,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_58]),
    [final]).

cnf(c_0_79,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_58]),
    [final]).

cnf(c_0_80,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_61]),
    [final]).

cnf(c_0_81,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39]),
    [final]).

cnf(c_0_82,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_62]),
    [final]).

cnf(c_0_83,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_63]),
    [final]).

cnf(c_0_84,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_64]),
    [final]).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_65]),
    [final]).

fof(c_0_86,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_56]),
    [final]).

fof(c_0_88,plain,(
    ! [X39,X40] :
      ( ( ~ v1_partfun1(X40,X39)
        | k1_relat_1(X40) = X39
        | ~ v1_relat_1(X40)
        | ~ v4_relat_1(X40,X39) )
      & ( k1_relat_1(X40) != X39
        | v1_partfun1(X40,X39)
        | ~ v1_relat_1(X40)
        | ~ v4_relat_1(X40,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_66]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_93,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68]),
    [final]).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_95,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_96,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_97,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72]),
    [final]).

fof(c_0_98,plain,(
    ! [X57] :
      ( ( m1_yellow_0(esk3_1(X57),X57)
        | v2_struct_0(X57)
        | ~ l1_orders_2(X57) )
      & ( ~ v2_struct_0(esk3_1(X57))
        | v2_struct_0(X57)
        | ~ l1_orders_2(X57) )
      & ( v1_orders_2(esk3_1(X57))
        | v2_struct_0(X57)
        | ~ l1_orders_2(X57) )
      & ( v4_yellow_0(esk3_1(X57),X57)
        | v2_struct_0(X57)
        | ~ l1_orders_2(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_yellow_0])])])])])).

cnf(c_0_99,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_100,plain,(
    ! [X36,X37,X38] :
      ( ( v1_funct_1(X38)
        | ~ v1_funct_1(X38)
        | ~ v1_partfun1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v1_funct_2(X38,X36,X37)
        | ~ v1_funct_1(X38)
        | ~ v1_partfun1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_101,plain,(
    ! [X44,X45,X46] :
      ( ( v1_funct_1(k2_funct_1(X46))
        | ~ v2_funct_1(X46)
        | k2_relset_1(X44,X45,X46) != X45
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(k2_funct_1(X46),X45,X44)
        | ~ v2_funct_1(X46)
        | k2_relset_1(X44,X45,X46) != X45
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(k2_funct_1(X46),k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | ~ v2_funct_1(X46)
        | k2_relset_1(X44,X45,X46) != X45
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_102,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74]),
    [final]).

cnf(c_0_103,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_75]),
    [final]).

cnf(c_0_104,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_76]),
    [final]).

cnf(c_0_105,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_77]),
    [final]).

cnf(c_0_106,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_78]),
    [final]).

cnf(c_0_107,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_79]),
    [final]).

cnf(c_0_108,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_80]),
    [final]).

cnf(c_0_109,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_81]),
    [final]).

cnf(c_0_110,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_82]),
    [final]).

cnf(c_0_111,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_83]),
    [final]).

cnf(c_0_112,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_84]),
    [final]).

cnf(c_0_113,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_64]),
    [final]).

cnf(c_0_114,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_47]),
    [final]).

cnf(c_0_115,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_58]),
    [final]).

cnf(c_0_116,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_58]),
    [final]).

cnf(c_0_117,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_39]),
    [final]).

cnf(c_0_118,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_119,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | m1_subset_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_85]),
    [final]).

cnf(c_0_120,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86]),
    [final]).

cnf(c_0_121,plain,
    ( m1_subset_1(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_87]),
    [final]).

cnf(c_0_122,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_partfun1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_92])]),
    [final]).

cnf(c_0_124,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_90]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_90]),
    [final]).

cnf(c_0_126,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95]),
    [final]).

cnf(c_0_127,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_96,c_0_97]),
    [final]).

cnf(c_0_128,plain,
    ( m1_yellow_0(esk3_1(X1),X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | k2_relat_1(k2_funct_1(esk6_0)) != u1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_130,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_99,c_0_97]),
    [final]).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_90]),
    [final]).

cnf(c_0_132,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_133,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_100]),
    [final]).

cnf(c_0_134,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_135,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_101]),
    [final]).

cnf(c_0_136,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))
    | k2_relset_1(X2,X3,esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X4)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_102]),
    [final]).

cnf(c_0_137,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k2_relset_1(X3,X4,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_103]),
    [final]).

cnf(c_0_138,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_101]),
    [final]).

cnf(c_0_139,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X4)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_104]),
    [final]).

cnf(c_0_140,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X4)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_105]),
    [final]).

cnf(c_0_141,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_57,c_0_106]),
    [final]).

cnf(c_0_142,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_107]),
    [final]).

cnf(c_0_143,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_101]),
    [final]).

cnf(c_0_144,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relset_1(X3,X4,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_75]),
    [final]).

cnf(c_0_145,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_108]),
    [final]).

cnf(c_0_146,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_109]),
    [final]).

cnf(c_0_147,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4) ),
    inference(spm,[status(thm)],[c_0_57,c_0_76]),
    [final]).

cnf(c_0_148,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_110]),
    [final]).

cnf(c_0_149,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_77]),
    [final]).

cnf(c_0_150,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_57,c_0_78]),
    [final]).

cnf(c_0_151,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_79]),
    [final]).

cnf(c_0_152,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_111]),
    [final]).

cnf(c_0_153,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) = k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_112]),
    [final]).

cnf(c_0_154,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) = k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_113]),
    [final]).

cnf(c_0_155,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_114]),
    [final]).

cnf(c_0_156,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_115]),
    [final]).

cnf(c_0_157,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) = k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_116]),
    [final]).

cnf(c_0_158,plain,
    ( k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_82]),
    [final]).

cnf(c_0_159,plain,
    ( k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3)),esk1_2(k2_zfmisc_1(X1,X2),X3)) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_117]),
    [final]).

cnf(c_0_160,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_83]),
    [final]).

cnf(c_0_161,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_84]),
    [final]).

cnf(c_0_162,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_64]),
    [final]).

cnf(c_0_163,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47]),
    [final]).

cnf(c_0_164,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_165,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_102]),
    [final]).

cnf(c_0_166,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_103]),
    [final]).

cnf(c_0_167,plain,
    ( k2_relset_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_zfmisc_1(X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_119]),
    [final]).

cnf(c_0_168,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_104]),
    [final]).

cnf(c_0_169,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_105]),
    [final]).

cnf(c_0_170,plain,
    ( k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_80]),
    [final]).

cnf(c_0_171,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_106]),
    [final]).

cnf(c_0_172,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_107]),
    [final]).

cnf(c_0_173,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_108]),
    [final]).

cnf(c_0_174,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_109]),
    [final]).

cnf(c_0_175,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_81]),
    [final]).

cnf(c_0_176,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_110]),
    [final]).

cnf(c_0_177,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_111]),
    [final]).

cnf(c_0_178,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_112]),
    [final]).

cnf(c_0_179,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_118,c_0_113]),
    [final]).

cnf(c_0_180,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_114]),
    [final]).

cnf(c_0_181,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_115]),
    [final]).

cnf(c_0_182,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_116]),
    [final]).

cnf(c_0_183,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3)) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39]),
    [final]).

cnf(c_0_184,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_117]),
    [final]).

cnf(c_0_185,plain,
    ( k2_relset_1(X1,X2,esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_zfmisc_1(X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_85]),
    [final]).

cnf(c_0_186,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r1_tarski(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119]),
    [final]).

cnf(c_0_187,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4) ),
    inference(spm,[status(thm)],[c_0_59,c_0_78]),
    [final]).

cnf(c_0_188,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_79]),
    [final]).

cnf(c_0_189,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_64]),
    [final]).

cnf(c_0_190,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_64]),
    [final]).

cnf(c_0_191,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47]),
    [final]).

cnf(c_0_192,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_47]),
    [final]).

cnf(c_0_193,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_93,c_0_64]),
    [final]).

cnf(c_0_194,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k1_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_120]),
    [final]).

cnf(c_0_195,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86]),
    [final]).

cnf(c_0_196,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_47]),
    [final]).

cnf(c_0_197,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_198,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_58]),
    [final]).

cnf(c_0_199,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31]),
    [final]).

cnf(c_0_200,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39]),
    [final]).

cnf(c_0_201,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_39]),
    [final]).

cnf(c_0_202,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_39]),
    [final]).

cnf(c_0_203,plain,
    ( k2_relset_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) = k2_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_121]),
    [final]).

cnf(c_0_204,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_41]),
    [final]).

cnf(c_0_205,plain,
    ( k2_relset_1(X1,X2,k2_zfmisc_1(X1,X2)) = k2_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_87]),
    [final]).

cnf(c_0_206,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124]),c_0_125])]),
    [final]).

cnf(c_0_207,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_126]),
    [final]).

cnf(c_0_208,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_orders_2(esk3_1(X1)),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128]),
    [final]).

cnf(c_0_209,negated_conjecture,
    ( k1_relat_1(esk6_0) != u1_struct_0(esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0)
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_120]),c_0_92])]),c_0_125])]),
    [final]).

cnf(c_0_210,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_121]),
    [final]).

cnf(c_0_211,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(esk3_1(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_128]),
    [final]).

cnf(c_0_212,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0),esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_131]),
    [final]).

cnf(c_0_213,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_132]),
    [final]).

cnf(c_0_214,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_131]),
    [final]).

cnf(c_0_215,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_90]),
    [final]).

cnf(c_0_216,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_90]),
    [final]).

cnf(c_0_217,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))
    | ~ v1_partfun1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_131]),c_0_92])]),
    [final]).

cnf(c_0_218,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_126]),
    [final]).

cnf(c_0_219,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71]),
    [final]).

cnf(c_0_220,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[c_0_134])).

fof(c_0_221,plain,(
    ! [X47] :
      ( v2_struct_0(X47)
      | ~ l1_struct_0(X47)
      | ~ v1_xboole_0(u1_struct_0(X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_222,plain,(
    ! [X48] :
      ( ~ l1_orders_2(X48)
      | l1_struct_0(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_223,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_126]),
    [final]).

cnf(c_0_224,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_126]),
    [final]).

cnf(c_0_225,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X3)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_102]),
    [final]).

cnf(c_0_226,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_137]),c_0_103]),
    [final]).

cnf(c_0_227,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_136]),c_0_102]),
    [final]).

cnf(c_0_228,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_137]),c_0_103]),
    [final]).

cnf(c_0_229,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_139]),c_0_104]),
    [final]).

cnf(c_0_230,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_140]),c_0_105]),
    [final]).

cnf(c_0_231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_141]),c_0_106]),
    [final]).

cnf(c_0_232,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_104]),
    [final]).

cnf(c_0_233,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_140]),c_0_105]),
    [final]).

cnf(c_0_234,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_141]),c_0_106]),
    [final]).

cnf(c_0_235,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_142]),c_0_107]),
    [final]).

cnf(c_0_236,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_142]),c_0_107]),
    [final]).

cnf(c_0_237,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_136]),c_0_102]),
    [final]).

cnf(c_0_238,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_137]),c_0_103]),
    [final]).

cnf(c_0_239,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_144]),c_0_74]),
    [final]).

cnf(c_0_240,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_144]),c_0_75]),
    [final]).

cnf(c_0_241,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X4,X3)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_144]),c_0_74]),
    [final]).

cnf(c_0_242,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_144]),c_0_75]),
    [final]).

cnf(c_0_243,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_139]),c_0_104]),
    [final]).

cnf(c_0_244,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_145]),c_0_108]),
    [final]).

cnf(c_0_245,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_146]),c_0_109]),
    [final]).

cnf(c_0_246,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_140]),c_0_105]),
    [final]).

cnf(c_0_247,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_141]),c_0_106]),
    [final]).

cnf(c_0_248,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_142]),c_0_107]),
    [final]).

cnf(c_0_249,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_145]),c_0_108]),
    [final]).

cnf(c_0_250,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_74]),
    [final]).

cnf(c_0_251,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_75]),
    [final]).

cnf(c_0_252,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_147]),c_0_76]),
    [final]).

cnf(c_0_253,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_148]),c_0_110]),
    [final]).

cnf(c_0_254,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_146]),c_0_109]),
    [final]).

cnf(c_0_255,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_149]),c_0_77]),
    [final]).

cnf(c_0_256,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_150]),c_0_78]),
    [final]).

cnf(c_0_257,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_151]),c_0_79]),
    [final]).

cnf(c_0_258,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_147]),c_0_76]),
    [final]).

cnf(c_0_259,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_149]),c_0_77]),
    [final]).

cnf(c_0_260,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_150]),c_0_78]),
    [final]).

cnf(c_0_261,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_151]),c_0_79]),
    [final]).

cnf(c_0_262,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_152]),c_0_111]),
    [final]).

cnf(c_0_263,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_148]),c_0_110]),
    [final]).

cnf(c_0_264,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_153]),c_0_112]),
    [final]).

cnf(c_0_265,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_154]),c_0_113]),
    [final]).

cnf(c_0_266,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_155]),c_0_114]),
    [final]).

cnf(c_0_267,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_147]),c_0_76]),
    [final]).

cnf(c_0_268,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_149]),c_0_77]),
    [final]).

cnf(c_0_269,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_150]),c_0_78]),
    [final]).

cnf(c_0_270,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_151]),c_0_79]),
    [final]).

cnf(c_0_271,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_156]),c_0_115]),
    [final]).

cnf(c_0_272,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_152]),c_0_111]),
    [final]).

cnf(c_0_273,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_157]),c_0_116]),
    [final]).

cnf(c_0_274,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_153]),c_0_112]),
    [final]).

cnf(c_0_275,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_148]),c_0_110]),
    [final]).

cnf(c_0_276,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_154]),c_0_113]),
    [final]).

cnf(c_0_277,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_155]),c_0_114]),
    [final]).

cnf(c_0_278,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_156]),c_0_115]),
    [final]).

cnf(c_0_279,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_145]),c_0_108]),
    [final]).

cnf(c_0_280,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_157]),c_0_116]),
    [final]).

cnf(c_0_281,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_152]),c_0_111]),
    [final]).

cnf(c_0_282,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_146]),c_0_109]),
    [final]).

cnf(c_0_283,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_158]),c_0_82]),
    [final]).

cnf(c_0_284,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_158]),c_0_82]),
    [final]).

cnf(c_0_285,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_102]),
    [final]).

cnf(c_0_286,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_103]),
    [final]).

cnf(c_0_287,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_153]),c_0_112]),
    [final]).

cnf(c_0_288,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X2)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_159]),c_0_117]),
    [final]).

cnf(c_0_289,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_160]),c_0_83]),
    [final]).

cnf(c_0_290,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_160]),c_0_83]),
    [final]).

cnf(c_0_291,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_154]),c_0_113]),
    [final]).

cnf(c_0_292,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_155]),c_0_114]),
    [final]).

cnf(c_0_293,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_156]),c_0_115]),
    [final]).

cnf(c_0_294,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_157]),c_0_116]),
    [final]).

cnf(c_0_295,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_161]),c_0_84]),
    [final]).

cnf(c_0_296,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_159]),c_0_117]),
    [final]).

cnf(c_0_297,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_162]),c_0_64]),
    [final]).

cnf(c_0_298,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_163]),c_0_47]),
    [final]).

cnf(c_0_299,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_158]),c_0_82]),
    [final]).

cnf(c_0_300,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_74]),c_0_58]),
    [final]).

cnf(c_0_301,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_75]),c_0_58]),
    [final]).

cnf(c_0_302,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_161]),c_0_84]),
    [final]).

cnf(c_0_303,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_162]),c_0_64]),
    [final]).

cnf(c_0_304,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_74]),c_0_58]),
    [final]).

cnf(c_0_305,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_75]),c_0_58]),
    [final]).

cnf(c_0_306,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X2)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_104]),
    [final]).

cnf(c_0_307,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_163]),c_0_47]),
    [final]).

cnf(c_0_308,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_160]),c_0_83]),
    [final]).

cnf(c_0_309,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_105]),
    [final]).

cnf(c_0_310,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_106]),
    [final]).

cnf(c_0_311,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_107]),
    [final]).

cnf(c_0_312,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_161]),c_0_84]),
    [final]).

cnf(c_0_313,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165]),
    [final]).

cnf(c_0_314,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) = esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | ~ r1_tarski(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_166]),
    [final]).

cnf(c_0_315,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_162]),c_0_64]),
    [final]).

cnf(c_0_316,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_163]),c_0_47]),
    [final]).

cnf(c_0_317,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_167]),c_0_119]),
    [final]).

cnf(c_0_318,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_74]),c_0_58]),
    [final]).

cnf(c_0_319,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_75]),c_0_58]),
    [final]).

cnf(c_0_320,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_159]),c_0_117]),
    [final]).

cnf(c_0_321,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_102]),
    [final]).

cnf(c_0_322,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_103]),
    [final]).

cnf(c_0_323,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))) = esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X4)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_168]),
    [final]).

cnf(c_0_324,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))) = esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X4)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_169]),
    [final]).

cnf(c_0_325,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_170]),c_0_80]),
    [final]).

cnf(c_0_326,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_167]),c_0_119]),
    [final]).

cnf(c_0_327,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_171]),
    [final]).

cnf(c_0_328,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_172]),
    [final]).

cnf(c_0_329,plain,
    ( k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_110]),
    [final]).

cnf(c_0_330,plain,
    ( k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_xboole_0
    | esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_108]),
    [final]).

cnf(c_0_331,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_74]),
    [final]).

cnf(c_0_332,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_75]),
    [final]).

cnf(c_0_333,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_104]),
    [final]).

cnf(c_0_334,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_170]),c_0_80]),
    [final]).

cnf(c_0_335,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_111]),
    [final]).

cnf(c_0_336,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_105]),
    [final]).

cnf(c_0_337,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_106]),
    [final]).

cnf(c_0_338,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_107]),
    [final]).

cnf(c_0_339,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_74]),
    [final]).

cnf(c_0_340,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_75]),
    [final]).

cnf(c_0_341,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_170]),c_0_80]),
    [final]).

cnf(c_0_342,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_167]),c_0_119]),
    [final]).

cnf(c_0_343,plain,
    ( k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(X1)
    | v1_partfun1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
    | ~ v1_funct_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_112]),
    [final]).

cnf(c_0_344,plain,
    ( k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(X1)
    | v1_partfun1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X1)
    | ~ v1_funct_2(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
    | ~ v1_funct_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_113]),
    [final]).

cnf(c_0_345,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k1_xboole_0
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1)
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_114]),
    [final]).

cnf(c_0_346,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k1_xboole_0
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_115]),
    [final]).

cnf(c_0_347,plain,
    ( k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(X1)
    | v1_partfun1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
    | ~ v1_funct_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_116]),
    [final]).

cnf(c_0_348,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_109]),
    [final]).

cnf(c_0_349,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_76]),
    [final]).

cnf(c_0_350,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) = esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_173]),
    [final]).

cnf(c_0_351,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_174]),
    [final]).

cnf(c_0_352,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_77]),
    [final]).

cnf(c_0_353,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_78]),
    [final]).

cnf(c_0_354,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_79]),
    [final]).

cnf(c_0_355,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_175]),c_0_81]),
    [final]).

cnf(c_0_356,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) = esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_176]),
    [final]).

cnf(c_0_357,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_165]),
    [final]).

cnf(c_0_358,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_166]),
    [final]).

cnf(c_0_359,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_175]),c_0_81]),
    [final]).

cnf(c_0_360,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_177]),
    [final]).

cnf(c_0_361,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_102]),
    [final]).

cnf(c_0_362,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_175]),c_0_81]),
    [final]).

cnf(c_0_363,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_103]),
    [final]).

cnf(c_0_364,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))) = esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2))
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_178]),
    [final]).

cnf(c_0_365,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_108]),
    [final]).

cnf(c_0_366,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_109]),
    [final]).

cnf(c_0_367,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_76]),
    [final]).

cnf(c_0_368,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_77]),
    [final]).

cnf(c_0_369,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_78]),
    [final]).

cnf(c_0_370,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_79]),
    [final]).

cnf(c_0_371,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))) = esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_179]),
    [final]).

cnf(c_0_372,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_180]),
    [final]).

cnf(c_0_373,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_110]),
    [final]).

cnf(c_0_374,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))) = esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_181]),
    [final]).

cnf(c_0_375,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))) = esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2))
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_182]),
    [final]).

cnf(c_0_376,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_112]),
    [final]).

cnf(c_0_377,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_113]),
    [final]).

cnf(c_0_378,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_114]),
    [final]).

cnf(c_0_379,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_115]),
    [final]).

cnf(c_0_380,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_111]),
    [final]).

cnf(c_0_381,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_116]),
    [final]).

cnf(c_0_382,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_168]),
    [final]).

cnf(c_0_383,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_169]),
    [final]).

cnf(c_0_384,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_171]),
    [final]).

cnf(c_0_385,plain,
    ( k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3)) = k1_xboole_0
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),X3),X1)
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),X3),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_117]),
    [final]).

cnf(c_0_386,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_172]),
    [final]).

cnf(c_0_387,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_183]),c_0_39]),
    [final]).

cnf(c_0_388,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X3,X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_183]),c_0_39]),
    [final]).

cnf(c_0_389,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_183]),c_0_39]),
    [final]).

cnf(c_0_390,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4) ),
    inference(spm,[status(thm)],[c_0_59,c_0_104]),
    [final]).

cnf(c_0_391,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_82]),
    [final]).

cnf(c_0_392,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_105]),
    [final]).

cnf(c_0_393,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_106]),
    [final]).

cnf(c_0_394,plain,
    ( k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_xboole_0
    | k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_119]),
    [final]).

cnf(c_0_395,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_107]),
    [final]).

cnf(c_0_396,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_82]),
    [final]).

cnf(c_0_397,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))) = esk1_2(k2_zfmisc_1(X1,X2),X3)
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))),esk1_2(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_184]),
    [final]).

cnf(c_0_398,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_84]),
    [final]).

cnf(c_0_399,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_84]),
    [final]).

cnf(c_0_400,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_117]),
    [final]).

cnf(c_0_401,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_185]),c_0_85]),
    [final]).

cnf(c_0_402,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) = esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_186]),
    [final]).

cnf(c_0_403,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_176]),
    [final]).

cnf(c_0_404,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_173]),
    [final]).

cnf(c_0_405,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_185]),c_0_85]),
    [final]).

cnf(c_0_406,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_177]),
    [final]).

cnf(c_0_407,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_174]),
    [final]).

cnf(c_0_408,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_185]),c_0_85]),
    [final]).

cnf(c_0_409,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_83]),
    [final]).

cnf(c_0_410,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_110]),
    [final]).

cnf(c_0_411,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_83]),
    [final]).

cnf(c_0_412,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_178]),
    [final]).

cnf(c_0_413,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_179]),
    [final]).

cnf(c_0_414,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_64]),
    [final]).

cnf(c_0_415,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_180]),
    [final]).

cnf(c_0_416,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_64]),
    [final]).

cnf(c_0_417,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | ~ v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_119]),
    [final]).

cnf(c_0_418,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_181]),
    [final]).

cnf(c_0_419,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = X3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | ~ r1_tarski(X3,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_162]),
    [final]).

cnf(c_0_420,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X3 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_58]),
    [final]).

cnf(c_0_421,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_182]),
    [final]).

cnf(c_0_422,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_111]),
    [final]).

cnf(c_0_423,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_58]),
    [final]).

cnf(c_0_424,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)) = X3
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_163]),
    [final]).

cnf(c_0_425,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_58]),
    [final]).

cnf(c_0_426,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(ef,[status(thm)],[c_0_187]),
    [final]).

cnf(c_0_427,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_78]),
    [final]).

cnf(c_0_428,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_112]),
    [final]).

cnf(c_0_429,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_58]),
    [final]).

cnf(c_0_430,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_79]),
    [final]).

cnf(c_0_431,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X1,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(ef,[status(thm)],[c_0_188]),
    [final]).

cnf(c_0_432,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_108]),
    [final]).

cnf(c_0_433,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_109]),
    [final]).

cnf(c_0_434,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_113]),
    [final]).

cnf(c_0_435,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X3 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_47]),
    [final]).

cnf(c_0_436,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_114]),
    [final]).

cnf(c_0_437,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_115]),
    [final]).

cnf(c_0_438,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_116]),
    [final]).

cnf(c_0_439,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_47]),
    [final]).

cnf(c_0_440,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_184]),
    [final]).

cnf(c_0_441,plain,
    ( esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(X1)
    | v5_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X3)
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_189]),
    [final]).

cnf(c_0_442,plain,
    ( esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(X1)
    | v4_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_190]),
    [final]).

cnf(c_0_443,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)) = X3
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X2)
    | ~ r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_191]),
    [final]).

cnf(c_0_444,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)) = X3
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1)
    | ~ r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_192]),
    [final]).

cnf(c_0_445,plain,
    ( esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(X1)
    | v1_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_193]),
    [final]).

cnf(c_0_446,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_194,c_0_195]),
    [final]).

cnf(c_0_447,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)) = X3
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | ~ r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_196]),
    [final]).

cnf(c_0_448,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_80]),
    [final]).

cnf(c_0_449,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_84]),
    [final]).

cnf(c_0_450,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_117]),
    [final]).

cnf(c_0_451,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_80]),
    [final]).

cnf(c_0_452,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_84]),
    [final]).

cnf(c_0_453,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_81]),
    [final]).

cnf(c_0_454,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_82]),
    [final]).

cnf(c_0_455,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3)) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_197,c_0_183]),
    [final]).

cnf(c_0_456,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_81]),
    [final]).

cnf(c_0_457,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_83]),
    [final]).

cnf(c_0_458,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_58]),
    [final]).

cnf(c_0_459,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = X1
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))
    | ~ r1_tarski(X1,esk1_2(k1_xboole_0,k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_62]),
    [final]).

cnf(c_0_460,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = X1
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_63]),
    [final]).

cnf(c_0_461,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X3 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_39]),
    [final]).

cnf(c_0_462,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_186]),
    [final]).

cnf(c_0_463,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_198]),
    [final]).

cnf(c_0_464,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = k1_xboole_0
    | esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = X1
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | ~ r1_tarski(X1,esk1_2(k1_xboole_0,k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_61]),
    [final]).

cnf(c_0_465,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = X1
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_199]),
    [final]).

cnf(c_0_466,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_82]),
    [final]).

cnf(c_0_467,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_197,c_0_200]),
    [final]).

cnf(c_0_468,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_39]),
    [final]).

cnf(c_0_469,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_83]),
    [final]).

cnf(c_0_470,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_80]),
    [final]).

cnf(c_0_471,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_80]),
    [final]).

cnf(c_0_472,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_81]),
    [final]).

cnf(c_0_473,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_81]),
    [final]).

cnf(c_0_474,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_197,c_0_201]),
    [final]).

cnf(c_0_475,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_84]),
    [final]).

cnf(c_0_476,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v5_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_119]),
    [final]).

cnf(c_0_477,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_62]),
    [final]).

cnf(c_0_478,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_82]),
    [final]).

cnf(c_0_479,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_83]),
    [final]).

cnf(c_0_480,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_197,c_0_202]),
    [final]).

cnf(c_0_481,plain,
    ( m1_subset_1(k2_funct_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_zfmisc_1(X1,X2)),X1)))
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_203]),c_0_121])]),
    [final]).

cnf(c_0_482,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X2
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_204]),
    [final]).

cnf(c_0_483,plain,
    ( v1_funct_2(k2_funct_1(k2_zfmisc_1(X1,X2)),k2_relat_1(k2_zfmisc_1(X1,X2)),X1)
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_203]),c_0_121])]),
    [final]).

cnf(c_0_484,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 = k1_xboole_0
    | v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_85]),
    [final]).

cnf(c_0_485,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X1
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_51]),
    [final]).

cnf(c_0_486,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_63]),
    [final]).

cnf(c_0_487,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_80]),
    [final]).

cnf(c_0_488,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_81]),
    [final]).

cnf(c_0_489,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X2
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X1)
    | ~ r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_51]),
    [final]).

cnf(c_0_490,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X1
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_64]),
    [final]).

cnf(c_0_491,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_85]),
    [final]).

cnf(c_0_492,plain,
    ( esk1_2(X1,k1_zfmisc_1(X2)) = X2
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X1)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_47]),
    [final]).

cnf(c_0_493,plain,
    ( m1_subset_1(k2_funct_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(k2_zfmisc_1(X1,X2)) != X2
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)
    | ~ v2_funct_1(k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_205]),c_0_87])]),
    [final]).

cnf(c_0_494,plain,
    ( v1_funct_2(k2_funct_1(k2_zfmisc_1(X1,X2)),X2,X1)
    | k2_relat_1(k2_zfmisc_1(X1,X2)) != X2
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)
    | ~ v2_funct_1(k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_205]),c_0_87])]),
    [final]).

cnf(c_0_495,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_194,c_0_56]),
    [final]).

cnf(c_0_496,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(esk6_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(u1_struct_0(esk4_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_206]),c_0_92]),c_0_125])]),
    [final]).

cnf(c_0_497,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [final]).

cnf(c_0_498,plain,
    ( v1_funct_1(k2_funct_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_zfmisc_1(X1,X2)) != X2
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)
    | ~ v2_funct_1(k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_205]),c_0_87])]),
    [final]).

cnf(c_0_499,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),X1)))
    | ~ v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_207]),c_0_126])])]),
    [final]).

cnf(c_0_500,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | v1_partfun1(k2_zfmisc_1(X1,X2),X1)
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_121]),
    [final]).

cnf(c_0_501,plain,
    ( u1_orders_2(esk3_1(X1)) = u1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(esk3_1(X1))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_208]),
    [final]).

cnf(c_0_502,plain,
    ( v1_funct_1(k2_funct_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_203]),c_0_121])]),
    [final]).

cnf(c_0_503,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(X1,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_31]),
    [final]).

cnf(c_0_504,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X1)
    | ~ v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_207]),c_0_126])])]),
    [final]).

cnf(c_0_505,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0)
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_209,c_0_206]),
    [final]).

cnf(c_0_506,plain,
    ( k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(X1,X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_210]),
    [final]).

cnf(c_0_507,plain,
    ( esk2_1(k1_zfmisc_1(X1)) = X1
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk2_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_65]),
    [final]).

cnf(c_0_508,plain,
    ( u1_struct_0(esk3_1(X1)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_1(X1))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_211]),
    [final]).

cnf(c_0_509,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_207]),c_0_126])])]),
    [final]).

cnf(c_0_510,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(k2_zfmisc_1(X2,X1),X2)
    | ~ v1_funct_2(k2_zfmisc_1(X2,X1),X2,X1)
    | ~ v1_funct_1(k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_87]),
    [final]).

cnf(c_0_511,plain,
    ( v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(k2_zfmisc_1(X1,X2),X1)
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_121]),
    [final]).

cnf(c_0_512,plain,
    ( v2_struct_0(X1)
    | r2_hidden(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_208]),
    [final]).

cnf(c_0_513,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v5_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_85]),
    [final]).

cnf(c_0_514,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_208]),
    [final]).

cnf(c_0_515,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v4_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_85]),
    [final]).

cnf(c_0_516,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_85]),
    [final]).

cnf(c_0_517,plain,
    ( v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)
    | ~ v1_partfun1(k2_zfmisc_1(X1,X2),X1)
    | ~ v1_funct_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_87]),
    [final]).

cnf(c_0_518,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(k1_xboole_0,X2)
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_126]),
    [final]).

cnf(c_0_519,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_65]),
    [final]).

cnf(c_0_520,plain,
    ( v2_struct_0(X1)
    | r2_hidden(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_211]),
    [final]).

cnf(c_0_521,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_212]),c_0_92]),c_0_131])]),
    [final]).

cnf(c_0_522,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_211]),
    [final]).

cnf(c_0_523,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_213,c_0_195]),
    [final]).

cnf(c_0_524,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk6_0),k2_relat_1(esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_212]),c_0_92]),c_0_131])]),
    [final]).

cnf(c_0_525,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | v1_partfun1(esk6_0,u1_struct_0(esk4_0))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_131]),c_0_92])]),
    [final]).

cnf(c_0_526,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_126]),
    [final]).

cnf(c_0_527,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_214]),
    [final]).

cnf(c_0_528,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_215]),
    [final]).

cnf(c_0_529,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | k2_relat_1(esk6_0) != u1_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_216]),c_0_91]),c_0_92]),c_0_90])]),
    [final]).

cnf(c_0_530,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_212]),c_0_92]),c_0_131])]),
    [final]).

cnf(c_0_531,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_217,c_0_123]),
    [final]).

cnf(c_0_532,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | k2_relat_1(esk6_0) != u1_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_216]),c_0_91]),c_0_92]),c_0_90])]),
    [final]).

cnf(c_0_533,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0))
    | k2_relat_1(esk6_0) != u1_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_216]),c_0_91]),c_0_92]),c_0_90])]),
    [final]).

cnf(c_0_534,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_218]),
    [final]).

cnf(c_0_535,plain,
    ( l1_orders_2(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_128]),
    [final]).

cnf(c_0_536,plain,
    ( m1_yellow_0(X1,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_219,c_0_56]),c_0_56])]),
    [final]).

cnf(c_0_537,plain,
    ( v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_220]),
    [final]).

cnf(c_0_538,plain,
    ( v4_yellow_0(esk3_1(X1),X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98]),
    [final]).

cnf(c_0_539,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | esk2_1(X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_540,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_221]),
    [final]).

cnf(c_0_541,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk3_1(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98]),
    [final]).

cnf(c_0_542,plain,
    ( v1_orders_2(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98]),
    [final]).

cnf(c_0_543,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_222]),
    [final]).

cnf(c_0_544,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_545,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_546,plain,
    ( r2_hidden(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_210]),
    [final]).

cnf(c_0_547,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),k2_relat_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_121]),
    [final]).

cnf(c_0_548,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_214]),
    [final]).

cnf(c_0_549,negated_conjecture,
    ( v5_relat_1(esk6_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_131]),
    [final]).

cnf(c_0_550,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_218]),
    [final]).

cnf(c_0_551,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_215]),
    [final]).

cnf(c_0_552,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_223]),c_0_224])]),
    [final]).

cnf(c_0_553,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_218]),
    [final]).

cnf(c_0_554,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_87]),
    [final]).

cnf(c_0_555,plain,
    ( v4_relat_1(k2_zfmisc_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_87]),
    [final]).

cnf(c_0_556,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_126]),
    [final]).

cnf(c_0_557,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_87]),
    [final]).

cnf(c_0_558,negated_conjecture,
    ( v5_relat_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_90]),
    [final]).

cnf(c_0_559,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_56]),
    [final]).

cnf(c_0_560,negated_conjecture,
    ( v23_waybel_0(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_561,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).

cnf(c_0_562,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.48  # and selection function SelectNewComplexAHPNS.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.029 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # No proof found!
% 0.19/0.48  # SZS status CounterSatisfiable
% 0.19/0.48  # SZS output start Saturation
% 0.19/0.48  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.19/0.48  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.48  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.19/0.48  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 0.19/0.48  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.48  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.19/0.48  fof(t67_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_waybel_0)).
% 0.19/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.48  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.19/0.48  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.48  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.19/0.48  fof(dt_m1_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 0.19/0.48  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.48  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.48  fof(rc4_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>?[X2]:(((m1_yellow_0(X2,X1)&~(v2_struct_0(X2)))&v1_orders_2(X2))&v4_yellow_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_yellow_0)).
% 0.19/0.48  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.48  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.48  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.48  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.48  fof(c_0_24, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk1_2(X14,X15),X15)|~r1_tarski(esk1_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk1_2(X14,X15),X15)|r1_tarski(esk1_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.48  fof(c_0_25, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  fof(c_0_26, plain, ![X49, X50, X51]:((X50=k1_xboole_0|~r2_hidden(X50,X49)|k3_tarski(X49)!=k1_xboole_0)&((esk2_1(X51)!=k1_xboole_0|k3_tarski(X51)=k1_xboole_0)&(r2_hidden(esk2_1(X51),X51)|k3_tarski(X51)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.19/0.48  fof(c_0_27, plain, ![X17]:k3_tarski(k1_zfmisc_1(X17))=X17, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.48  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.19/0.48  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_tarski(esk1_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.19/0.48  cnf(c_0_32, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.19/0.48  cnf(c_0_33, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.19/0.48  cnf(c_0_34, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_28]), ['final']).
% 0.19/0.48  fof(c_0_35, plain, ![X8, X9]:(v1_xboole_0(X9)|(~r1_tarski(X9,X8)|~r1_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.19/0.48  fof(c_0_36, plain, ![X7]:r1_xboole_0(X7,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.48  fof(c_0_37, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_29]), ['final']).
% 0.19/0.48  cnf(c_0_39, plain, (X1=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,X1),k1_zfmisc_1(X2))|r2_hidden(esk1_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31]), ['final']).
% 0.19/0.48  cnf(c_0_40, plain, (X1=k1_xboole_0|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])]), ['final']).
% 0.19/0.48  cnf(c_0_41, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))|r2_hidden(esk1_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_34, c_0_31]), ['final']).
% 0.19/0.48  cnf(c_0_42, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.48  cnf(c_0_43, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.19/0.48  fof(c_0_44, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))|(~r1_tarski(k2_relat_1(X35),X33)|m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.19/0.48  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  fof(c_0_46, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.48  cnf(c_0_47, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['final']).
% 0.19/0.48  fof(c_0_48, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.48  cnf(c_0_49, plain, (esk1_2(k1_xboole_0,X1)=k1_xboole_0|X1=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['final']).
% 0.19/0.48  cnf(c_0_50, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.19/0.48  cnf(c_0_51, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_31]), ['final']).
% 0.19/0.48  cnf(c_0_52, plain, (r2_hidden(esk2_1(X1),X1)|k3_tarski(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.19/0.48  fof(c_0_53, plain, ![X41, X42, X43]:((X42=k1_xboole_0|v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(X41!=k1_xboole_0|v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.19/0.48  fof(c_0_54, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t67_waybel_0])).
% 0.19/0.48  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.19/0.48  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45]), ['final']).
% 0.19/0.48  cnf(c_0_57, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46]), ['final']).
% 0.19/0.48  cnf(c_0_58, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_59, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_48]), ['final']).
% 0.19/0.48  cnf(c_0_60, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48]), ['final']).
% 0.19/0.48  cnf(c_0_61, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=k1_xboole_0|k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_49]), ['final']).
% 0.19/0.48  cnf(c_0_62, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))|r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51]), ['final']).
% 0.19/0.48  cnf(c_0_63, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))|r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51]), ['final']).
% 0.19/0.48  cnf(c_0_64, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)), inference(spm,[status(thm)],[c_0_30, c_0_51]), ['final']).
% 0.19/0.48  cnf(c_0_65, plain, (X1=k1_xboole_0|r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_52]), c_0_33]), ['final']).
% 0.19/0.48  cnf(c_0_66, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.48  fof(c_0_67, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_orders_2(esk4_0))&((~v2_struct_0(esk5_0)&l1_orders_2(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(v23_waybel_0(esk6_0,esk4_0,esk5_0)&(~v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|k2_relat_1(k2_funct_1(esk6_0))!=u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_54])])])])).
% 0.19/0.48  fof(c_0_68, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.48  fof(c_0_69, plain, ![X19]:m1_subset_1(k1_subset_1(X19),k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.19/0.48  fof(c_0_70, plain, ![X18]:k1_subset_1(X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.48  fof(c_0_71, plain, ![X53, X54]:(((r1_tarski(u1_struct_0(X54),u1_struct_0(X53))|~m1_yellow_0(X54,X53)|~l1_orders_2(X54)|~l1_orders_2(X53))&(r1_tarski(u1_orders_2(X54),u1_orders_2(X53))|~m1_yellow_0(X54,X53)|~l1_orders_2(X54)|~l1_orders_2(X53)))&(~r1_tarski(u1_struct_0(X54),u1_struct_0(X53))|~r1_tarski(u1_orders_2(X54),u1_orders_2(X53))|m1_yellow_0(X54,X53)|~l1_orders_2(X54)|~l1_orders_2(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.19/0.48  fof(c_0_72, plain, ![X55, X56]:(~l1_orders_2(X55)|(~m1_yellow_0(X56,X55)|l1_orders_2(X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).
% 0.19/0.48  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.19/0.48  cnf(c_0_74, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_75, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_76, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_77, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_78, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_59, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_79, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_60, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_80, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=k1_xboole_0|k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_61]), ['final']).
% 0.19/0.48  cnf(c_0_81, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_82, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_62]), ['final']).
% 0.19/0.48  cnf(c_0_83, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_30, c_0_63]), ['final']).
% 0.19/0.48  cnf(c_0_84, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_85, plain, (X1=k1_xboole_0|m1_subset_1(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_65]), ['final']).
% 0.19/0.48  fof(c_0_86, plain, ![X22]:((k2_relat_1(X22)=k1_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_relat_1(X22)=k2_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.48  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_56]), ['final']).
% 0.19/0.48  fof(c_0_88, plain, ![X39, X40]:((~v1_partfun1(X40,X39)|k1_relat_1(X40)=X39|(~v1_relat_1(X40)|~v4_relat_1(X40,X39)))&(k1_relat_1(X40)!=X39|v1_partfun1(X40,X39)|(~v1_relat_1(X40)|~v4_relat_1(X40,X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.48  cnf(c_0_89, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_66]), ['final']).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_92, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_93, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_68]), ['final']).
% 0.19/0.48  cnf(c_0_94, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.48  cnf(c_0_95, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.48  cnf(c_0_96, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.48  cnf(c_0_97, plain, (l1_orders_2(X2)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72]), ['final']).
% 0.19/0.48  fof(c_0_98, plain, ![X57]:((((m1_yellow_0(esk3_1(X57),X57)|(v2_struct_0(X57)|~l1_orders_2(X57)))&(~v2_struct_0(esk3_1(X57))|(v2_struct_0(X57)|~l1_orders_2(X57))))&(v1_orders_2(esk3_1(X57))|(v2_struct_0(X57)|~l1_orders_2(X57))))&(v4_yellow_0(esk3_1(X57),X57)|(v2_struct_0(X57)|~l1_orders_2(X57)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_yellow_0])])])])])).
% 0.19/0.48  cnf(c_0_99, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.48  fof(c_0_100, plain, ![X36, X37, X38]:((v1_funct_1(X38)|(~v1_funct_1(X38)|~v1_partfun1(X38,X36))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v1_funct_2(X38,X36,X37)|(~v1_funct_1(X38)|~v1_partfun1(X38,X36))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.48  fof(c_0_101, plain, ![X44, X45, X46]:(((v1_funct_1(k2_funct_1(X46))|(~v2_funct_1(X46)|k2_relset_1(X44,X45,X46)!=X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(v1_funct_2(k2_funct_1(X46),X45,X44)|(~v2_funct_1(X46)|k2_relset_1(X44,X45,X46)!=X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&(m1_subset_1(k2_funct_1(X46),k1_zfmisc_1(k2_zfmisc_1(X45,X44)))|(~v2_funct_1(X46)|k2_relset_1(X44,X45,X46)!=X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.48  cnf(c_0_102, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))))), inference(spm,[status(thm)],[c_0_73, c_0_74]), ['final']).
% 0.19/0.48  cnf(c_0_103, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_104, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_105, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_106, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_107, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_108, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_109, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))))), inference(spm,[status(thm)],[c_0_73, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_110, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_73, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_111, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_73, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_112, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_73, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_113, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_73, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_114, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_73, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_115, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_116, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_73, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_117, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_73, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_118, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.19/0.48  cnf(c_0_119, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|m1_subset_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_73, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_120, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86]), ['final']).
% 0.19/0.48  cnf(c_0_121, plain, (m1_subset_1(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2)))))), inference(spm,[status(thm)],[c_0_73, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_122, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_88]), ['final']).
% 0.19/0.48  cnf(c_0_123, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_partfun1(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_92])]), ['final']).
% 0.19/0.48  cnf(c_0_124, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_90]), ['final']).
% 0.19/0.48  cnf(c_0_125, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_93, c_0_90]), ['final']).
% 0.19/0.48  cnf(c_0_126, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_94, c_0_95]), ['final']).
% 0.19/0.48  cnf(c_0_127, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_96, c_0_97]), ['final']).
% 0.19/0.48  cnf(c_0_128, plain, (m1_yellow_0(esk3_1(X1),X1)|v2_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_98]), ['final']).
% 0.19/0.48  cnf(c_0_129, negated_conjecture, (~v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|k2_relat_1(k2_funct_1(esk6_0))!=u1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_130, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_99, c_0_97]), ['final']).
% 0.19/0.48  cnf(c_0_131, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))))), inference(spm,[status(thm)],[c_0_73, c_0_90]), ['final']).
% 0.19/0.48  cnf(c_0_132, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.48  cnf(c_0_133, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_100]), ['final']).
% 0.19/0.48  cnf(c_0_134, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.48  cnf(c_0_135, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_101]), ['final']).
% 0.19/0.48  cnf(c_0_136, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))|k2_relset_1(X2,X3,esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))|k1_zfmisc_1(k2_zfmisc_1(X1,X4))=k1_zfmisc_1(k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_57, c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_137, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k2_relset_1(X3,X4,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_138, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_101]), ['final']).
% 0.19/0.48  cnf(c_0_139, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))|k1_zfmisc_1(k2_zfmisc_1(X1,X4))=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X3)), inference(spm,[status(thm)],[c_0_57, c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_140, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))|k1_zfmisc_1(k2_zfmisc_1(X1,X4))=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X2)), inference(spm,[status(thm)],[c_0_57, c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_141, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_57, c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_142, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_57, c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_143, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_101]), ['final']).
% 0.19/0.48  cnf(c_0_144, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relset_1(X3,X4,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_57, c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_145, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_146, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_147, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)), inference(spm,[status(thm)],[c_0_57, c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_148, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_57, c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_149, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_57, c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_150, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_57, c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_151, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_57, c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_152, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_57, c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_153, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))|k1_zfmisc_1(k2_zfmisc_1(X1,X3))=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_57, c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_154, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))|k1_zfmisc_1(k2_zfmisc_1(X1,X3))=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),X2)), inference(spm,[status(thm)],[c_0_57, c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_155, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)), inference(spm,[status(thm)],[c_0_57, c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_156, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_157, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))|k1_zfmisc_1(k2_zfmisc_1(X1,X3))=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_57, c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_158, plain, (k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_57, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_159, plain, (k2_relset_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3)),esk1_2(k2_zfmisc_1(X1,X2),X3))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)), inference(spm,[status(thm)],[c_0_57, c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_160, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_57, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_161, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_162, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_57, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_163, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)), inference(spm,[status(thm)],[c_0_57, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_164, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.48  cnf(c_0_165, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))))), inference(spm,[status(thm)],[c_0_118, c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_166, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_167, plain, (k2_relset_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_zfmisc_1(X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_168, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_169, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_170, plain, (k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_171, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_172, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r1_tarski(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_173, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_174, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))))), inference(spm,[status(thm)],[c_0_118, c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_175, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_176, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_177, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))))), inference(spm,[status(thm)],[c_0_118, c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_178, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_179, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_118, c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_180, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_118, c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_181, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))))), inference(spm,[status(thm)],[c_0_118, c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_182, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_183, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)), inference(spm,[status(thm)],[c_0_57, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_184, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))))), inference(spm,[status(thm)],[c_0_118, c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_185, plain, (k2_relset_1(X1,X2,esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_zfmisc_1(X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_186, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r1_tarski(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))), inference(spm,[status(thm)],[c_0_118, c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_187, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)), inference(spm,[status(thm)],[c_0_59, c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_188, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_60, c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_189, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_59, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_190, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_60, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_191, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_59, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_192, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_193, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_93, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_194, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r1_tarski(k1_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_55, c_0_120]), ['final']).
% 0.19/0.48  cnf(c_0_195, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86]), ['final']).
% 0.19/0.48  cnf(c_0_196, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_93, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_197, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(esk1_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.19/0.48  cnf(c_0_198, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_93, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_199, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_31]), ['final']).
% 0.19/0.48  cnf(c_0_200, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_59, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_201, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_60, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_202, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_93, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_203, plain, (k2_relset_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))=k2_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_121]), ['final']).
% 0.19/0.48  cnf(c_0_204, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_41]), ['final']).
% 0.19/0.48  cnf(c_0_205, plain, (k2_relset_1(X1,X2,k2_zfmisc_1(X1,X2))=k2_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_206, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124]), c_0_125])]), ['final']).
% 0.19/0.48  cnf(c_0_207, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_208, plain, (v2_struct_0(X1)|r1_tarski(u1_orders_2(esk3_1(X1)),u1_orders_2(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_127, c_0_128]), ['final']).
% 0.19/0.48  cnf(c_0_209, negated_conjecture, (k1_relat_1(esk6_0)!=u1_struct_0(esk4_0)|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)|~v1_funct_1(k2_funct_1(esk6_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_120]), c_0_92])]), c_0_125])]), ['final']).
% 0.19/0.48  cnf(c_0_210, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_118, c_0_121]), ['final']).
% 0.19/0.48  cnf(c_0_211, plain, (v2_struct_0(X1)|r1_tarski(u1_struct_0(esk3_1(X1)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_130, c_0_128]), ['final']).
% 0.19/0.48  cnf(c_0_212, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0),esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_131]), ['final']).
% 0.19/0.48  cnf(c_0_213, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_132]), ['final']).
% 0.19/0.48  cnf(c_0_214, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))), inference(spm,[status(thm)],[c_0_118, c_0_131]), ['final']).
% 0.19/0.48  cnf(c_0_215, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_118, c_0_90]), ['final']).
% 0.19/0.48  cnf(c_0_216, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_90]), ['final']).
% 0.19/0.48  cnf(c_0_217, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))|~v1_partfun1(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_131]), c_0_92])]), ['final']).
% 0.19/0.48  cnf(c_0_218, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_118, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_219, plain, (m1_yellow_0(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_71]), ['final']).
% 0.19/0.48  cnf(c_0_220, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[c_0_134])).
% 0.19/0.48  fof(c_0_221, plain, ![X47]:(v2_struct_0(X47)|~l1_struct_0(X47)|~v1_xboole_0(u1_struct_0(X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.48  fof(c_0_222, plain, ![X48]:(~l1_orders_2(X48)|l1_struct_0(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.48  cnf(c_0_223, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_224, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_225, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X3)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_226, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_137]), c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_227, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_136]), c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_228, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_137]), c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_229, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_139]), c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_230, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_140]), c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_231, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_141]), c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_232, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_233, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_140]), c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_234, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_141]), c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_235, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_142]), c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_236, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_142]), c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_237, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_136]), c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_238, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_137]), c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_239, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_144]), c_0_74]), ['final']).
% 0.19/0.48  cnf(c_0_240, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_144]), c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_241, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X4,X3)|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_144]), c_0_74]), ['final']).
% 0.19/0.48  cnf(c_0_242, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_144]), c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_243, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_139]), c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_244, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_145]), c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_245, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_146]), c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_246, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_140]), c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_247, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_141]), c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_248, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_142]), c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_249, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_145]), c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_250, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_74]), ['final']).
% 0.19/0.48  cnf(c_0_251, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_252, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_147]), c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_253, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_148]), c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_254, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_146]), c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_255, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_149]), c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_256, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_150]), c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_257, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_151]), c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_258, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_147]), c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_259, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_149]), c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_260, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_150]), c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_261, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_151]), c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_262, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_152]), c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_263, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_148]), c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_264, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_153]), c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_265, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_154]), c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_266, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_155]), c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_267, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_147]), c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_268, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_149]), c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_269, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_150]), c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_270, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_151]), c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_271, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_156]), c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_272, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_152]), c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_273, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_157]), c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_274, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_153]), c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_275, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_148]), c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_276, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_154]), c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_277, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_155]), c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_278, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_156]), c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_279, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_145]), c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_280, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_157]), c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_281, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_152]), c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_282, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_146]), c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_283, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_158]), c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_284, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_158]), c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_285, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_89, c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_286, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_287, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_153]), c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_288, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X2)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_159]), c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_289, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_160]), c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_290, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_160]), c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_291, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_154]), c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_292, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_155]), c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_293, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_156]), c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_294, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_157]), c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_295, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_161]), c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_296, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_159]), c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_297, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_162]), c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_298, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_163]), c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_299, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_158]), c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_300, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_74]), c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_301, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_75]), c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_302, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_161]), c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_303, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_162]), c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_304, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_74]), c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_305, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_75]), c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_306, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X2)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_89, c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_307, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_163]), c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_308, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_160]), c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_309, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_89, c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_310, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_89, c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_311, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_89, c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_312, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_161]), c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_313, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|~r1_tarski(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_164, c_0_165]), ['final']).
% 0.19/0.48  cnf(c_0_314, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))=esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|~r1_tarski(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_164, c_0_166]), ['final']).
% 0.19/0.48  cnf(c_0_315, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_162]), c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_316, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_163]), c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_317, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|m1_subset_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)))|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_167]), c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_318, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_74]), c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_319, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_75]), c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_320, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_159]), c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_321, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|~v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_133, c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_322, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_323, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))))=esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|k1_zfmisc_1(k2_zfmisc_1(X1,X4))=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X3)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), inference(spm,[status(thm)],[c_0_164, c_0_168]), ['final']).
% 0.19/0.48  cnf(c_0_324, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))))=esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|k1_zfmisc_1(k2_zfmisc_1(X1,X4))=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))),X2)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))),esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), inference(spm,[status(thm)],[c_0_164, c_0_169]), ['final']).
% 0.19/0.48  cnf(c_0_325, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_170]), c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_326, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_2(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1)|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_167]), c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_327, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_164, c_0_171]), ['final']).
% 0.19/0.48  cnf(c_0_328, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_164, c_0_172]), ['final']).
% 0.19/0.48  cnf(c_0_329, plain, (k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_330, plain, (k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k1_xboole_0|esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_331, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_89, c_0_74]), ['final']).
% 0.19/0.48  cnf(c_0_332, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_333, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_334, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_170]), c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_335, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_89, c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_336, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_337, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_338, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_339, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_133, c_0_74]), ['final']).
% 0.19/0.48  cnf(c_0_340, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_75]), ['final']).
% 0.19/0.48  cnf(c_0_341, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_170]), c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_342, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_167]), c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_343, plain, (k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X2,X3))=k1_zfmisc_1(X1)|v1_partfun1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)|r2_hidden(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))|~v1_funct_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(spm,[status(thm)],[c_0_89, c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_344, plain, (k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X2,X3))=k1_zfmisc_1(X1)|v1_partfun1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)|r1_tarski(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X1)|~v1_funct_2(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))|~v1_funct_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(spm,[status(thm)],[c_0_89, c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_345, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k1_xboole_0|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1)|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_89, c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_346, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k1_xboole_0|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1)|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_89, c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_347, plain, (k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X2,X3))=k1_zfmisc_1(X1)|v1_partfun1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))|~v1_funct_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(spm,[status(thm)],[c_0_89, c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_348, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k1_xboole_0|esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_89, c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_349, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_350, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))=esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_164, c_0_173]), ['final']).
% 0.19/0.48  cnf(c_0_351, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))|esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_164, c_0_174]), ['final']).
% 0.19/0.48  cnf(c_0_352, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_353, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_354, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_355, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_175]), c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_356, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))=esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_164, c_0_176]), ['final']).
% 0.19/0.48  cnf(c_0_357, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))))), inference(spm,[status(thm)],[c_0_34, c_0_165]), ['final']).
% 0.19/0.48  cnf(c_0_358, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_166]), ['final']).
% 0.19/0.48  cnf(c_0_359, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_175]), c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_360, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_164, c_0_177]), ['final']).
% 0.19/0.48  cnf(c_0_361, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))), inference(spm,[status(thm)],[c_0_59, c_0_102]), ['final']).
% 0.19/0.48  cnf(c_0_362, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_175]), c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_363, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(spm,[status(thm)],[c_0_59, c_0_103]), ['final']).
% 0.19/0.48  cnf(c_0_364, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))=esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|k1_zfmisc_1(k2_zfmisc_1(X1,X3))=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2))|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), inference(spm,[status(thm)],[c_0_164, c_0_178]), ['final']).
% 0.19/0.48  cnf(c_0_365, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_366, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|~v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_133, c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_367, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_76]), ['final']).
% 0.19/0.48  cnf(c_0_368, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_77]), ['final']).
% 0.19/0.48  cnf(c_0_369, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_370, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_371, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))=esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|k1_zfmisc_1(k2_zfmisc_1(X1,X3))=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),X2)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), inference(spm,[status(thm)],[c_0_164, c_0_179]), ['final']).
% 0.19/0.48  cnf(c_0_372, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_164, c_0_180]), ['final']).
% 0.19/0.48  cnf(c_0_373, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_374, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))))=esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))),esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_164, c_0_181]), ['final']).
% 0.19/0.48  cnf(c_0_375, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))=esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|k1_zfmisc_1(k2_zfmisc_1(X1,X3))=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))),k1_zfmisc_1(X2))|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),esk1_2(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), inference(spm,[status(thm)],[c_0_164, c_0_182]), ['final']).
% 0.19/0.48  cnf(c_0_376, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_377, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_378, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_133, c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_379, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_133, c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_380, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_133, c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_381, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_382, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_168]), ['final']).
% 0.19/0.48  cnf(c_0_383, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_169]), ['final']).
% 0.19/0.48  cnf(c_0_384, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_171]), ['final']).
% 0.19/0.48  cnf(c_0_385, plain, (k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))=k1_xboole_0|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),X3),X1)|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),X3),X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_89, c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_386, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_172]), ['final']).
% 0.19/0.48  cnf(c_0_387, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_183]), c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_388, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X3,X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_183]), c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_389, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_183]), c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_390, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)), inference(spm,[status(thm)],[c_0_59, c_0_104]), ['final']).
% 0.19/0.48  cnf(c_0_391, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_392, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_59, c_0_105]), ['final']).
% 0.19/0.48  cnf(c_0_393, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_59, c_0_106]), ['final']).
% 0.19/0.48  cnf(c_0_394, plain, (k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k1_xboole_0|k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_395, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_59, c_0_107]), ['final']).
% 0.19/0.48  cnf(c_0_396, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_397, plain, (k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3)))=esk1_2(k2_zfmisc_1(X1,X2),X3)|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))),esk1_2(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_164, c_0_184]), ['final']).
% 0.19/0.48  cnf(c_0_398, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|X2=k1_xboole_0|v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_399, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_400, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(spm,[status(thm)],[c_0_133, c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_401, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|m1_subset_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_185]), c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_402, plain, (k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))=esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_164, c_0_186]), ['final']).
% 0.19/0.48  cnf(c_0_403, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_34, c_0_176]), ['final']).
% 0.19/0.48  cnf(c_0_404, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_173]), ['final']).
% 0.19/0.48  cnf(c_0_405, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_2(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_185]), c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_406, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_34, c_0_177]), ['final']).
% 0.19/0.48  cnf(c_0_407, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))))), inference(spm,[status(thm)],[c_0_34, c_0_174]), ['final']).
% 0.19/0.48  cnf(c_0_408, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_185]), c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_409, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_89, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_410, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_59, c_0_110]), ['final']).
% 0.19/0.48  cnf(c_0_411, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_133, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_412, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_34, c_0_178]), ['final']).
% 0.19/0.48  cnf(c_0_413, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_34, c_0_179]), ['final']).
% 0.19/0.48  cnf(c_0_414, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|X2=k1_xboole_0|v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_415, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_34, c_0_180]), ['final']).
% 0.19/0.48  cnf(c_0_416, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_417, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|~v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_418, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))))), inference(spm,[status(thm)],[c_0_34, c_0_181]), ['final']).
% 0.19/0.48  cnf(c_0_419, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=X3|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|~r1_tarski(X3,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_164, c_0_162]), ['final']).
% 0.19/0.48  cnf(c_0_420, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|X3=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_89, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_421, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_182]), ['final']).
% 0.19/0.48  cnf(c_0_422, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_59, c_0_111]), ['final']).
% 0.19/0.48  cnf(c_0_423, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_133, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_424, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))=X3|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|~r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_164, c_0_163]), ['final']).
% 0.19/0.48  cnf(c_0_425, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|X2=k1_xboole_0|v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_426, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(ef,[status(thm)],[c_0_187]), ['final']).
% 0.19/0.48  cnf(c_0_427, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_60, c_0_78]), ['final']).
% 0.19/0.48  cnf(c_0_428, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_59, c_0_112]), ['final']).
% 0.19/0.48  cnf(c_0_429, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_430, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_59, c_0_79]), ['final']).
% 0.19/0.48  cnf(c_0_431, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X1,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(ef,[status(thm)],[c_0_188]), ['final']).
% 0.19/0.48  cnf(c_0_432, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(spm,[status(thm)],[c_0_59, c_0_108]), ['final']).
% 0.19/0.48  cnf(c_0_433, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))), inference(spm,[status(thm)],[c_0_59, c_0_109]), ['final']).
% 0.19/0.48  cnf(c_0_434, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_59, c_0_113]), ['final']).
% 0.19/0.48  cnf(c_0_435, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|X3=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_89, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_436, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_59, c_0_114]), ['final']).
% 0.19/0.48  cnf(c_0_437, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_115]), ['final']).
% 0.19/0.48  cnf(c_0_438, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_59, c_0_116]), ['final']).
% 0.19/0.48  cnf(c_0_439, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_133, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_440, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_34, c_0_184]), ['final']).
% 0.19/0.48  cnf(c_0_441, plain, (esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=X1|k1_zfmisc_1(k2_zfmisc_1(X2,X3))=k1_zfmisc_1(X1)|v5_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X3)|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(spm,[status(thm)],[c_0_164, c_0_189]), ['final']).
% 0.19/0.48  cnf(c_0_442, plain, (esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=X1|k1_zfmisc_1(k2_zfmisc_1(X2,X3))=k1_zfmisc_1(X1)|v4_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(spm,[status(thm)],[c_0_164, c_0_190]), ['final']).
% 0.19/0.48  cnf(c_0_443, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))=X3|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X2)|~r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_164, c_0_191]), ['final']).
% 0.19/0.48  cnf(c_0_444, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))=X3|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X1)|~r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_164, c_0_192]), ['final']).
% 0.19/0.48  cnf(c_0_445, plain, (esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=X1|k1_zfmisc_1(k2_zfmisc_1(X2,X3))=k1_zfmisc_1(X1)|v1_relat_1(esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(spm,[status(thm)],[c_0_164, c_0_193]), ['final']).
% 0.19/0.48  cnf(c_0_446, plain, (m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_194, c_0_195]), ['final']).
% 0.19/0.48  cnf(c_0_447, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))=X3|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|~r1_tarski(X3,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))), inference(spm,[status(thm)],[c_0_164, c_0_196]), ['final']).
% 0.19/0.48  cnf(c_0_448, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_449, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_59, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_450, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_59, c_0_117]), ['final']).
% 0.19/0.48  cnf(c_0_451, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_452, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_60, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_453, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_89, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_454, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_60, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_455, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|~r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_197, c_0_183]), ['final']).
% 0.19/0.48  cnf(c_0_456, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_133, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_457, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_60, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_458, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_58]), ['final']).
% 0.19/0.48  cnf(c_0_459, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=X1|k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))|~r1_tarski(X1,esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_164, c_0_62]), ['final']).
% 0.19/0.48  cnf(c_0_460, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=X1|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_164, c_0_63]), ['final']).
% 0.19/0.48  cnf(c_0_461, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|X3=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(spm,[status(thm)],[c_0_89, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_462, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))))), inference(spm,[status(thm)],[c_0_34, c_0_186]), ['final']).
% 0.19/0.48  cnf(c_0_463, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_93, c_0_198]), ['final']).
% 0.19/0.48  cnf(c_0_464, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=k1_xboole_0|esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=X1|k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|~r1_tarski(X1,esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_164, c_0_61]), ['final']).
% 0.19/0.48  cnf(c_0_465, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=X1|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_164, c_0_199]), ['final']).
% 0.19/0.48  cnf(c_0_466, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_59, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_467, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)|~r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_197, c_0_200]), ['final']).
% 0.19/0.48  cnf(c_0_468, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(spm,[status(thm)],[c_0_133, c_0_39]), ['final']).
% 0.19/0.48  cnf(c_0_469, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_59, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_470, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_59, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_471, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_60, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_472, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_59, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_473, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_474, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|~r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_197, c_0_201]), ['final']).
% 0.19/0.48  cnf(c_0_475, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_93, c_0_84]), ['final']).
% 0.19/0.48  cnf(c_0_476, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v5_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(spm,[status(thm)],[c_0_59, c_0_119]), ['final']).
% 0.19/0.48  cnf(c_0_477, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_62]), ['final']).
% 0.19/0.48  cnf(c_0_478, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_93, c_0_82]), ['final']).
% 0.19/0.48  cnf(c_0_479, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_93, c_0_83]), ['final']).
% 0.19/0.48  cnf(c_0_480, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_197, c_0_202]), ['final']).
% 0.19/0.48  cnf(c_0_481, plain, (m1_subset_1(k2_funct_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_zfmisc_1(X1,X2)),X1)))|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))|~v2_funct_1(k2_zfmisc_1(X1,X2))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_203]), c_0_121])]), ['final']).
% 0.19/0.48  cnf(c_0_482, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X2|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))|~r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_164, c_0_204]), ['final']).
% 0.19/0.48  cnf(c_0_483, plain, (v1_funct_2(k2_funct_1(k2_zfmisc_1(X1,X2)),k2_relat_1(k2_zfmisc_1(X1,X2)),X1)|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))|~v2_funct_1(k2_zfmisc_1(X1,X2))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_203]), c_0_121])]), ['final']).
% 0.19/0.48  cnf(c_0_484, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2=k1_xboole_0|v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_89, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_485, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X1|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_164, c_0_51]), ['final']).
% 0.19/0.48  cnf(c_0_486, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_34, c_0_63]), ['final']).
% 0.19/0.48  cnf(c_0_487, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_93, c_0_80]), ['final']).
% 0.19/0.48  cnf(c_0_488, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_93, c_0_81]), ['final']).
% 0.19/0.48  cnf(c_0_489, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X2|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X1)|~r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_164, c_0_51]), ['final']).
% 0.19/0.48  cnf(c_0_490, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X1|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X2))|~r1_tarski(X1,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_164, c_0_64]), ['final']).
% 0.19/0.48  cnf(c_0_491, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_133, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_492, plain, (esk1_2(X1,k1_zfmisc_1(X2))=X2|k1_zfmisc_1(X2)=k1_zfmisc_1(X1)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))|~r1_tarski(X2,esk1_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_164, c_0_47]), ['final']).
% 0.19/0.48  cnf(c_0_493, plain, (m1_subset_1(k2_funct_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(k2_zfmisc_1(X1,X2))!=X2|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)|~v2_funct_1(k2_zfmisc_1(X1,X2))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_205]), c_0_87])]), ['final']).
% 0.19/0.48  cnf(c_0_494, plain, (v1_funct_2(k2_funct_1(k2_zfmisc_1(X1,X2)),X2,X1)|k2_relat_1(k2_zfmisc_1(X1,X2))!=X2|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)|~v2_funct_1(k2_zfmisc_1(X1,X2))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_205]), c_0_87])]), ['final']).
% 0.19/0.48  cnf(c_0_495, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_194, c_0_56]), ['final']).
% 0.19/0.48  cnf(c_0_496, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v2_funct_1(esk6_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~r1_tarski(u1_struct_0(esk4_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_206]), c_0_92]), c_0_125])]), ['final']).
% 0.19/0.48  cnf(c_0_497, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['final']).
% 0.19/0.48  cnf(c_0_498, plain, (v1_funct_1(k2_funct_1(k2_zfmisc_1(X1,X2)))|k2_relat_1(k2_zfmisc_1(X1,X2))!=X2|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)|~v2_funct_1(k2_zfmisc_1(X1,X2))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_205]), c_0_87])]), ['final']).
% 0.19/0.48  cnf(c_0_499, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),X1)))|~v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_207]), c_0_126])])]), ['final']).
% 0.19/0.48  cnf(c_0_500, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=k1_xboole_0|v1_partfun1(k2_zfmisc_1(X1,X2),X1)|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_89, c_0_121]), ['final']).
% 0.19/0.48  cnf(c_0_501, plain, (u1_orders_2(esk3_1(X1))=u1_orders_2(X1)|v2_struct_0(X1)|~l1_orders_2(X1)|~r1_tarski(u1_orders_2(X1),u1_orders_2(esk3_1(X1)))), inference(spm,[status(thm)],[c_0_164, c_0_208]), ['final']).
% 0.19/0.48  cnf(c_0_502, plain, (v1_funct_1(k2_funct_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))|~v2_funct_1(k2_zfmisc_1(X1,X2))|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_203]), c_0_121])]), ['final']).
% 0.19/0.48  cnf(c_0_503, plain, (esk1_2(X1,X2)=X1|X2=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(X1,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_164, c_0_31]), ['final']).
% 0.19/0.48  cnf(c_0_504, plain, (v1_funct_2(k2_funct_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X1)|~v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_207]), c_0_126])])]), ['final']).
% 0.19/0.48  cnf(c_0_505, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)|~v1_funct_1(k2_funct_1(esk6_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_209, c_0_206]), ['final']).
% 0.19/0.48  cnf(c_0_506, plain, (k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2)))=k2_zfmisc_1(X1,X2)|~r1_tarski(k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2))),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_164, c_0_210]), ['final']).
% 0.19/0.48  cnf(c_0_507, plain, (esk2_1(k1_zfmisc_1(X1))=X1|X1=k1_xboole_0|~r1_tarski(X1,esk2_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_164, c_0_65]), ['final']).
% 0.19/0.48  cnf(c_0_508, plain, (u1_struct_0(esk3_1(X1))=u1_struct_0(X1)|v2_struct_0(X1)|~l1_orders_2(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_1(X1)))), inference(spm,[status(thm)],[c_0_164, c_0_211]), ['final']).
% 0.19/0.48  cnf(c_0_509, plain, (v1_funct_1(k2_funct_1(k1_xboole_0))|~v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_207]), c_0_126])])]), ['final']).
% 0.19/0.48  cnf(c_0_510, plain, (X1=k1_xboole_0|v1_partfun1(k2_zfmisc_1(X2,X1),X2)|~v1_funct_2(k2_zfmisc_1(X2,X1),X2,X1)|~v1_funct_1(k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_89, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_511, plain, (v1_funct_2(k2_zfmisc_1(X1,X2),X1,k2_relat_1(k2_zfmisc_1(X1,X2)))|~v1_partfun1(k2_zfmisc_1(X1,X2),X1)|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_133, c_0_121]), ['final']).
% 0.19/0.48  cnf(c_0_512, plain, (v2_struct_0(X1)|r2_hidden(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_208]), ['final']).
% 0.19/0.48  cnf(c_0_513, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v5_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_59, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_514, plain, (v2_struct_0(X1)|m1_subset_1(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_30, c_0_208]), ['final']).
% 0.19/0.48  cnf(c_0_515, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v4_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_60, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_516, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_93, c_0_85]), ['final']).
% 0.19/0.48  cnf(c_0_517, plain, (v1_funct_2(k2_zfmisc_1(X1,X2),X1,X2)|~v1_partfun1(k2_zfmisc_1(X1,X2),X1)|~v1_funct_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_133, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_518, plain, (X1=k1_xboole_0|v1_partfun1(k1_xboole_0,X2)|~v1_funct_2(k1_xboole_0,X2,X1)|~v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_519, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_65]), ['final']).
% 0.19/0.48  cnf(c_0_520, plain, (v2_struct_0(X1)|r2_hidden(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_211]), ['final']).
% 0.19/0.48  cnf(c_0_521, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_212]), c_0_92]), c_0_131])]), ['final']).
% 0.19/0.48  cnf(c_0_522, plain, (v2_struct_0(X1)|m1_subset_1(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_30, c_0_211]), ['final']).
% 0.19/0.48  cnf(c_0_523, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_213, c_0_195]), ['final']).
% 0.19/0.48  cnf(c_0_524, negated_conjecture, (v1_funct_2(k2_funct_1(esk6_0),k2_relat_1(esk6_0),u1_struct_0(esk4_0))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_212]), c_0_92]), c_0_131])]), ['final']).
% 0.19/0.48  cnf(c_0_525, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|v1_partfun1(esk6_0,u1_struct_0(esk4_0))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_131]), c_0_92])]), ['final']).
% 0.19/0.48  cnf(c_0_526, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)|~v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_133, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_527, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))=esk6_0|~r1_tarski(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_164, c_0_214]), ['final']).
% 0.19/0.48  cnf(c_0_528, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))=esk6_0|~r1_tarski(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_164, c_0_215]), ['final']).
% 0.19/0.48  cnf(c_0_529, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|k2_relat_1(esk6_0)!=u1_struct_0(esk5_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_216]), c_0_91]), c_0_92]), c_0_90])]), ['final']).
% 0.19/0.48  cnf(c_0_530, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_212]), c_0_92]), c_0_131])]), ['final']).
% 0.19/0.48  cnf(c_0_531, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_217, c_0_123]), ['final']).
% 0.19/0.48  cnf(c_0_532, negated_conjecture, (v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|k2_relat_1(esk6_0)!=u1_struct_0(esk5_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_216]), c_0_91]), c_0_92]), c_0_90])]), ['final']).
% 0.19/0.48  cnf(c_0_533, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))|k2_relat_1(esk6_0)!=u1_struct_0(esk5_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_216]), c_0_91]), c_0_92]), c_0_90])]), ['final']).
% 0.19/0.48  cnf(c_0_534, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_164, c_0_218]), ['final']).
% 0.19/0.48  cnf(c_0_535, plain, (l1_orders_2(esk3_1(X1))|v2_struct_0(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_97, c_0_128]), ['final']).
% 0.19/0.48  cnf(c_0_536, plain, (m1_yellow_0(X1,X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_219, c_0_56]), c_0_56])]), ['final']).
% 0.19/0.48  cnf(c_0_537, plain, (v1_partfun1(X1,k1_xboole_0)|~v1_funct_2(X1,k1_xboole_0,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_220]), ['final']).
% 0.19/0.48  cnf(c_0_538, plain, (v4_yellow_0(esk3_1(X1),X1)|v2_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_98]), ['final']).
% 0.19/0.48  cnf(c_0_539, plain, (k3_tarski(X1)=k1_xboole_0|esk2_1(X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.19/0.48  cnf(c_0_540, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_221]), ['final']).
% 0.19/0.48  cnf(c_0_541, plain, (v2_struct_0(X1)|~v2_struct_0(esk3_1(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_98]), ['final']).
% 0.19/0.48  cnf(c_0_542, plain, (v1_orders_2(esk3_1(X1))|v2_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_98]), ['final']).
% 0.19/0.48  cnf(c_0_543, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_222]), ['final']).
% 0.19/0.48  cnf(c_0_544, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_545, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_546, plain, (r2_hidden(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(k2_zfmisc_1(X1,X2)))))), inference(spm,[status(thm)],[c_0_34, c_0_210]), ['final']).
% 0.19/0.48  cnf(c_0_547, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),k2_relat_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_121]), ['final']).
% 0.19/0.48  cnf(c_0_548, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))))), inference(spm,[status(thm)],[c_0_34, c_0_214]), ['final']).
% 0.19/0.48  cnf(c_0_549, negated_conjecture, (v5_relat_1(esk6_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_59, c_0_131]), ['final']).
% 0.19/0.48  cnf(c_0_550, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_218]), ['final']).
% 0.19/0.48  cnf(c_0_551, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_34, c_0_215]), ['final']).
% 0.19/0.48  cnf(c_0_552, plain, (v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_223]), c_0_224])]), ['final']).
% 0.19/0.48  cnf(c_0_553, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_218]), ['final']).
% 0.19/0.48  cnf(c_0_554, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_59, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_555, plain, (v4_relat_1(k2_zfmisc_1(X1,X2),X1)), inference(spm,[status(thm)],[c_0_60, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_556, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_126]), ['final']).
% 0.19/0.48  cnf(c_0_557, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_93, c_0_87]), ['final']).
% 0.19/0.48  cnf(c_0_558, negated_conjecture, (v5_relat_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_59, c_0_90]), ['final']).
% 0.19/0.48  cnf(c_0_559, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_56]), ['final']).
% 0.19/0.48  cnf(c_0_560, negated_conjecture, (v23_waybel_0(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_561, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  cnf(c_0_562, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_67]), ['final']).
% 0.19/0.48  # SZS output end Saturation
% 0.19/0.48  # Proof object total steps             : 563
% 0.19/0.48  # Proof object clause steps            : 514
% 0.19/0.48  # Proof object formula steps           : 49
% 0.19/0.48  # Proof object conjectures             : 39
% 0.19/0.48  # Proof object clause conjectures      : 36
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 50
% 0.19/0.48  # Proof object initial formulas used   : 24
% 0.19/0.48  # Proof object generating inferences   : 454
% 0.19/0.48  # Proof object simplifying inferences  : 177
% 0.19/0.48  # Parsed axioms                        : 24
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 52
% 0.19/0.48  # Removed in clause preprocessing      : 2
% 0.19/0.48  # Initial clauses in saturation        : 50
% 0.19/0.48  # Processed clauses                    : 802
% 0.19/0.48  # ...of these trivial                  : 2
% 0.19/0.48  # ...subsumed                          : 242
% 0.19/0.48  # ...remaining for further processing  : 558
% 0.19/0.48  # Other redundant clauses eliminated   : 10
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 0
% 0.19/0.48  # Backward-rewritten                   : 0
% 0.19/0.48  # Generated clauses                    : 738
% 0.19/0.48  # ...of the previous two non-trivial   : 703
% 0.19/0.48  # Contextual simplify-reflections      : 104
% 0.19/0.48  # Paramodulations                      : 716
% 0.19/0.48  # Factorizations                       : 12
% 0.19/0.48  # Equation resolutions                 : 10
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 503
% 0.19/0.48  #    Positive orientable unit clauses  : 40
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 2
% 0.19/0.48  #    Non-unit-clauses                  : 461
% 0.19/0.48  # Current number of unprocessed clauses: 0
% 0.19/0.48  # ...number of literals in the above   : 0
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 50
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 122777
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 5950
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 346
% 0.19/0.48  # Unit Clause-clause subsumption calls : 389
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 29
% 0.19/0.48  # BW rewrite match successes           : 0
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 43138
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.138 s
% 0.19/0.48  # System time              : 0.007 s
% 0.19/0.48  # Total time               : 0.145 s
% 0.19/0.48  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
