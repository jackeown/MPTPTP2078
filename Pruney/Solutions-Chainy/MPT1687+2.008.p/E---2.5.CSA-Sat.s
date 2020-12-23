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
% DateTime   : Thu Dec  3 11:16:30 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  417 (8756 expanded)
%              Number of clauses        :  372 (3970 expanded)
%              Number of leaves         :   22 (2290 expanded)
%              Depth                    :    9
%              Number of atoms          : 1720 (43830 expanded)
%              Number of equality atoms :  407 (6917 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

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

fof(c_0_22,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X7)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r1_tarski(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | ~ r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_23,plain,(
    ! [X31,X32,X33] :
      ( ( X32 = k1_xboole_0
        | v1_partfun1(X33,X31)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_xboole_0
        | v1_partfun1(X33,X31)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( v1_xboole_0(X6)
      | ~ r1_tarski(X6,X5)
      | ~ r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_27,plain,(
    ! [X40,X41,X42] :
      ( ( X41 = k1_xboole_0
        | ~ r2_hidden(X41,X40)
        | k3_tarski(X40) != k1_xboole_0 )
      & ( esk2_1(X42) != k1_xboole_0
        | k3_tarski(X42) = k1_xboole_0 )
      & ( r2_hidden(esk2_1(X42),X42)
        | k3_tarski(X42) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_28,plain,(
    ! [X14] : k3_tarski(k1_zfmisc_1(X14)) = X14 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_31,plain,(
    ! [X37] :
      ( ( v1_funct_1(X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_2(X37,k1_relat_1(X37),k2_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X37),k2_relat_1(X37))))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_32,plain,(
    ! [X29,X30] :
      ( ( ~ v1_partfun1(X30,X29)
        | k1_relat_1(X30) = X29
        | ~ v1_relat_1(X30)
        | ~ v4_relat_1(X30,X29) )
      & ( k1_relat_1(X30) != X29
        | v1_partfun1(X30,X29)
        | ~ v1_relat_1(X30)
        | ~ v4_relat_1(X30,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_36,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_tarski(esk1_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

fof(c_0_41,plain,(
    ! [X4] : r1_xboole_0(X4,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_43,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_29]),
    [final]).

fof(c_0_45,plain,(
    ! [X34,X35,X36] :
      ( ( v1_funct_1(k2_funct_1(X36))
        | ~ v2_funct_1(X36)
        | k2_relset_1(X34,X35,X36) != X35
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v1_funct_2(k2_funct_1(X36),X35,X34)
        | ~ v2_funct_1(X36)
        | k2_relset_1(X34,X35,X36) != X35
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( m1_subset_1(k2_funct_1(X36),k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | ~ v2_funct_1(X36)
        | k2_relset_1(X34,X35,X36) != X35
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X34,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_46,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

fof(c_0_49,plain,(
    ! [X19] :
      ( ( k2_relat_1(X19) = k1_relat_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_relat_1(X19) = k2_relat_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_50,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_56,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_58,plain,
    ( X1 = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [final]).

cnf(c_0_59,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | v1_xboole_0(esk1_2(X2,X1))
    | ~ r1_xboole_0(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39]),
    [final]).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43])]),
    [final]).

cnf(c_0_62,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39]),
    [final]).

cnf(c_0_63,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_64,plain,
    ( k2_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1) = k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47]),
    [final]).

cnf(c_0_65,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47]),
    [final]).

cnf(c_0_67,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_68,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_69,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_70,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_71,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_47]),
    [final]).

cnf(c_0_72,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_partfun1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( v4_relat_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_53]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_53]),
    [final]).

fof(c_0_76,plain,(
    ! [X16] : m1_subset_1(k1_subset_1(X16),k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_77,plain,(
    ! [X15] : k1_subset_1(X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_78,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [final]).

cnf(c_0_79,plain,
    ( X1 = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60]),
    [final]).

cnf(c_0_80,plain,
    ( esk1_2(k1_xboole_0,X1) = k1_xboole_0
    | X1 = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62]),
    [final]).

cnf(c_0_81,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39]),
    [final]).

cnf(c_0_82,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_47]),c_0_65]),
    [final]).

cnf(c_0_83,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | k3_tarski(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_84,plain,
    ( r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_85,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_64]),c_0_47]),c_0_65]),
    [final]).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_66]),
    [final]).

cnf(c_0_88,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71]),
    [final]).

fof(c_0_89,plain,(
    ! [X44,X45] :
      ( ( r1_tarski(u1_struct_0(X45),u1_struct_0(X44))
        | ~ m1_yellow_0(X45,X44)
        | ~ l1_orders_2(X45)
        | ~ l1_orders_2(X44) )
      & ( r1_tarski(u1_orders_2(X45),u1_orders_2(X44))
        | ~ m1_yellow_0(X45,X44)
        | ~ l1_orders_2(X45)
        | ~ l1_orders_2(X44) )
      & ( ~ r1_tarski(u1_struct_0(X45),u1_struct_0(X44))
        | ~ r1_tarski(u1_orders_2(X45),u1_orders_2(X44))
        | m1_yellow_0(X45,X44)
        | ~ l1_orders_2(X45)
        | ~ l1_orders_2(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_90,plain,(
    ! [X46,X47] :
      ( ~ l1_orders_2(X46)
      | ~ m1_yellow_0(X47,X46)
      | l1_orders_2(X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(esk6_0) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])]),
    [final]).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_93,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_94,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_78]),
    [final]).

cnf(c_0_95,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_96,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_78]),
    [final]).

cnf(c_0_97,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_79]),
    [final]).

cnf(c_0_98,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_80]),
    [final]).

cnf(c_0_99,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_81]),
    [final]).

cnf(c_0_100,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_82]),
    [final]).

cnf(c_0_101,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_83]),c_0_43]),
    [final]).

cnf(c_0_102,plain,
    ( r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_103,plain,
    ( k2_relset_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)),k2_funct_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_67])).

cnf(c_0_104,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_67])).

cnf(c_0_105,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_67])).

cnf(c_0_106,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_85])).

cnf(c_0_107,plain,
    ( r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_67])).

cnf(c_0_108,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_69])).

cnf(c_0_109,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_67])).

cnf(c_0_110,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_111,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90]),
    [final]).

fof(c_0_112,plain,(
    ! [X48] :
      ( ( m1_yellow_0(esk3_1(X48),X48)
        | v2_struct_0(X48)
        | ~ l1_orders_2(X48) )
      & ( ~ v2_struct_0(esk3_1(X48))
        | v2_struct_0(X48)
        | ~ l1_orders_2(X48) )
      & ( v1_orders_2(esk3_1(X48))
        | v2_struct_0(X48)
        | ~ l1_orders_2(X48) )
      & ( v4_yellow_0(esk3_1(X48),X48)
        | v2_struct_0(X48)
        | ~ l1_orders_2(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_yellow_0])])])])])).

cnf(c_0_113,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | k2_relat_1(k2_funct_1(esk6_0)) != u1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_116,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93]),
    [final]).

cnf(c_0_117,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_94]),
    [final]).

cnf(c_0_118,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_94]),
    [final]).

cnf(c_0_119,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_94]),
    [final]).

cnf(c_0_120,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_94]),
    [final]).

cnf(c_0_121,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_94]),
    [final]).

cnf(c_0_122,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_60]),
    [final]).

cnf(c_0_123,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_97]),
    [final]).

cnf(c_0_124,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(X1)) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_98]),
    [final]).

cnf(c_0_125,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_58]),
    [final]).

cnf(c_0_126,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_99]),
    [final]).

cnf(c_0_127,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1),k2_funct_1(X1)) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_128,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_129,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_101]),
    [final]).

cnf(c_0_130,plain,
    ( r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_100]),
    [final]).

cnf(c_0_131,plain,
    ( r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_82]),
    [final]).

cnf(c_0_132,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_66]),
    [final]).

cnf(c_0_133,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_58]),
    [final]).

cnf(c_0_134,plain,
    ( k2_relset_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)),k2_funct_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_85])).

cnf(c_0_135,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_85])).

cnf(c_0_136,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_85])).

cnf(c_0_137,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_100]),
    [final]).

cnf(c_0_138,plain,
    ( r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_85])).

cnf(c_0_139,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_85])).

cnf(c_0_140,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_85])).

cnf(c_0_141,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_110,c_0_111]),
    [final]).

cnf(c_0_142,plain,
    ( m1_yellow_0(esk3_1(X1),X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112]),
    [final]).

cnf(c_0_143,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_113,c_0_111]),
    [final]).

cnf(c_0_144,negated_conjecture,
    ( k1_relat_1(esk6_0) != u1_struct_0(esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0)
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(esk6_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_69]),c_0_55])])).

cnf(c_0_145,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0),esk6_0) = k2_relat_1(esk6_0)
    | u1_struct_0(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_115]),
    [final]).

cnf(c_0_146,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_147,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_148,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_116]),
    [final]).

cnf(c_0_149,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relset_1(X3,X4,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_117]),
    [final]).

cnf(c_0_150,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_94]),
    [final]).

cnf(c_0_151,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_118]),
    [final]).

cnf(c_0_152,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_119]),
    [final]).

cnf(c_0_153,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_120]),
    [final]).

cnf(c_0_154,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_121]),
    [final]).

cnf(c_0_155,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_122]),
    [final]).

cnf(c_0_156,plain,
    ( k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_123]),
    [final]).

cnf(c_0_157,plain,
    ( k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_124]),
    [final]).

cnf(c_0_158,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_125]),
    [final]).

cnf(c_0_159,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_126]),
    [final]).

cnf(c_0_160,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_99]),
    [final]).

cnf(c_0_161,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_78]),
    [final]).

cnf(c_0_162,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3)) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_58]),
    [final]).

cnf(c_0_163,plain,
    ( k2_relset_1(k2_relat_1(X1),k1_relat_1(X1),k2_funct_1(X1)) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_67]),
    [final]).

cnf(c_0_164,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_64]),c_0_47]),c_0_65]),
    [final]).

cnf(c_0_165,plain,
    ( k2_relset_1(X1,X2,esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_zfmisc_1(X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_129]),
    [final]).

cnf(c_0_166,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4) ),
    inference(spm,[status(thm)],[c_0_95,c_0_120]),
    [final]).

cnf(c_0_167,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_95,c_0_99]),
    [final]).

cnf(c_0_168,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_121]),
    [final]).

cnf(c_0_169,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_99]),
    [final]).

cnf(c_0_170,plain,
    ( v1_xboole_0(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_130]),
    [final]).

cnf(c_0_171,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_78]),
    [final]).

cnf(c_0_172,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_78]),
    [final]).

cnf(c_0_173,plain,
    ( v1_xboole_0(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_131]),
    [final]).

cnf(c_0_174,plain,
    ( v1_xboole_0(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(X1),k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_175,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_99]),
    [final]).

cnf(c_0_176,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_133]),
    [final]).

cnf(c_0_177,plain,
    ( k2_relset_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)),k2_funct_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_100]),
    [final]).

cnf(c_0_178,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_135,c_0_100]),
    [final]).

cnf(c_0_179,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_136,c_0_100]),
    [final]).

cnf(c_0_180,plain,
    ( k2_relset_1(k2_relat_1(X1),k1_relat_1(X1),k2_funct_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_82]),
    [final]).

cnf(c_0_181,plain,
    ( r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_131]),
    [final]).

cnf(c_0_182,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1),k2_funct_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_137]),
    [final]).

cnf(c_0_183,plain,
    ( r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_100]),
    [final]).

cnf(c_0_184,plain,
    ( r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_185,plain,
    ( r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_186,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_62]),
    [final]).

cnf(c_0_187,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_188,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_139,c_0_100]),
    [final]).

cnf(c_0_189,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_94]),
    [final]).

cnf(c_0_190,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1)
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_122]),
    [final]).

cnf(c_0_191,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_140,c_0_100]),
    [final]).

cnf(c_0_192,plain,
    ( v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_82]),
    [final]).

cnf(c_0_193,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_58]),
    [final]).

cnf(c_0_194,plain,
    ( v5_relat_1(k2_funct_1(X1),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_82]),
    [final]).

cnf(c_0_195,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_58]),
    [final]).

cnf(c_0_196,plain,
    ( v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_137]),
    [final]).

cnf(c_0_197,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_116]),
    [final]).

cnf(c_0_198,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_39]),
    [final]).

cnf(c_0_199,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_orders_2(esk3_1(X1)),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142]),
    [final]).

cnf(c_0_200,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(esk3_1(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_143,c_0_142]),
    [final]).

cnf(c_0_201,negated_conjecture,
    ( k1_relat_1(esk6_0) != u1_struct_0(esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0)
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_75])]),
    [final]).

cnf(c_0_202,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_funct_1(k2_funct_1(esk6_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_145]),c_0_55])]),c_0_115]),c_0_146]),
    [final]).

cnf(c_0_203,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_115]),
    [final]).

cnf(c_0_204,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_53]),
    [final]).

cnf(c_0_205,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_53]),
    [final]).

cnf(c_0_206,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[c_0_147])).

fof(c_0_207,plain,(
    ! [X38] :
      ( v2_struct_0(X38)
      | ~ l1_struct_0(X38)
      | ~ v1_xboole_0(u1_struct_0(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_208,plain,(
    ! [X39] :
      ( ~ l1_orders_2(X39)
      | l1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_209,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_148])).

cnf(c_0_210,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_116]),
    [final]).

cnf(c_0_211,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_116]),
    [final]).

cnf(c_0_212,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_149]),c_0_150]),
    [final]).

cnf(c_0_213,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_149]),c_0_117]),
    [final]).

cnf(c_0_214,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X4,X3)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_149]),c_0_150]),
    [final]).

cnf(c_0_215,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_149]),c_0_117]),
    [final]).

cnf(c_0_216,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_149]),c_0_150]),
    [final]).

cnf(c_0_217,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_149]),c_0_117]),
    [final]).

cnf(c_0_218,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_151]),c_0_118]),
    [final]).

cnf(c_0_219,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_152]),c_0_119]),
    [final]).

cnf(c_0_220,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_153]),c_0_120]),
    [final]).

cnf(c_0_221,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_151]),c_0_118]),
    [final]).

cnf(c_0_222,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_152]),c_0_119]),
    [final]).

cnf(c_0_223,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_153]),c_0_120]),
    [final]).

cnf(c_0_224,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_154]),c_0_121]),
    [final]).

cnf(c_0_225,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_154]),c_0_121]),
    [final]).

cnf(c_0_226,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_151]),c_0_118]),
    [final]).

cnf(c_0_227,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_152]),c_0_119]),
    [final]).

cnf(c_0_228,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_153]),c_0_120]),
    [final]).

cnf(c_0_229,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X4
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_154]),c_0_121]),
    [final]).

cnf(c_0_230,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_155]),c_0_122]),
    [final]).

cnf(c_0_231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_156]),c_0_123]),
    [final]).

cnf(c_0_232,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_157]),c_0_124]),
    [final]).

cnf(c_0_233,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_158]),c_0_125]),
    [final]).

cnf(c_0_234,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_155]),c_0_122]),
    [final]).

cnf(c_0_235,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_156]),c_0_123]),
    [final]).

cnf(c_0_236,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_157]),c_0_124]),
    [final]).

cnf(c_0_237,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_157]),c_0_124]),
    [final]).

cnf(c_0_238,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_159]),c_0_126]),
    [final]).

cnf(c_0_239,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_160]),c_0_99]),
    [final]).

cnf(c_0_240,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_161]),c_0_78]),
    [final]).

cnf(c_0_241,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_150]),c_0_94]),
    [final]).

cnf(c_0_242,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_158]),c_0_125]),
    [final]).

cnf(c_0_243,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_155]),c_0_122]),
    [final]).

cnf(c_0_244,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_117]),c_0_94]),
    [final]).

cnf(c_0_245,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_159]),c_0_126]),
    [final]).

cnf(c_0_246,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_160]),c_0_99]),
    [final]).

cnf(c_0_247,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_161]),c_0_78]),
    [final]).

cnf(c_0_248,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_150]),c_0_94]),
    [final]).

cnf(c_0_249,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_117]),c_0_94]),
    [final]).

cnf(c_0_250,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_159]),c_0_126]),
    [final]).

cnf(c_0_251,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) != X2
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_158]),c_0_125]),
    [final]).

cnf(c_0_252,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_156]),c_0_123]),
    [final]).

cnf(c_0_253,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_160]),c_0_99]),
    [final]).

cnf(c_0_254,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_161]),c_0_78]),
    [final]).

cnf(c_0_255,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_150]),c_0_94]),
    [final]).

cnf(c_0_256,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_117]),c_0_94]),
    [final]).

cnf(c_0_257,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_150]),
    [final]).

cnf(c_0_258,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_117]),
    [final]).

cnf(c_0_259,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_162]),c_0_58]),
    [final]).

cnf(c_0_260,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_118]),
    [final]).

cnf(c_0_261,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_119]),
    [final]).

cnf(c_0_262,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_120]),
    [final]).

cnf(c_0_263,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | X4 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_121]),
    [final]).

cnf(c_0_264,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X3,X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_162]),c_0_58]),
    [final]).

cnf(c_0_265,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_122]),
    [final]).

cnf(c_0_266,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) != X3
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_162]),c_0_58]),
    [final]).

cnf(c_0_267,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_163]),c_0_82]),c_0_85]),c_0_164]),
    [final]).

cnf(c_0_268,plain,
    ( k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_160]),
    [final]).

cnf(c_0_269,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3))) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))
    | ~ r1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_161]),
    [final]).

cnf(c_0_270,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_163]),c_0_82]),c_0_85]),c_0_164]),
    [final]).

cnf(c_0_271,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_123]),
    [final]).

cnf(c_0_272,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_126]),
    [final]).

cnf(c_0_273,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_165]),c_0_129]),
    [final]).

cnf(c_0_274,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X2))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(ef,[status(thm)],[c_0_166]),
    [final]).

cnf(c_0_275,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_120]),
    [final]).

cnf(c_0_276,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_121]),
    [final]).

cnf(c_0_277,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_167]),
    [final]).

cnf(c_0_278,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X1,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(ef,[status(thm)],[c_0_168]),
    [final]).

cnf(c_0_279,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)
    | k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_165]),c_0_129]),
    [final]).

cnf(c_0_280,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_169]),
    [final]).

cnf(c_0_281,plain,
    ( v1_xboole_0(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_282,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_171]),
    [final]).

cnf(c_0_283,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_172]),
    [final]).

cnf(c_0_284,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_funct_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))
    | k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) != X2
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_165]),c_0_129]),
    [final]).

cnf(c_0_285,plain,
    ( v1_xboole_0(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_286,plain,
    ( v1_xboole_0(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_287,plain,
    ( v1_xboole_0(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_288,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_175]),
    [final]).

cnf(c_0_289,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_176]),
    [final]).

cnf(c_0_290,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_99]),
    [final]).

cnf(c_0_291,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_177]),c_0_178]),c_0_85]),c_0_179]),
    [final]).

cnf(c_0_292,plain,
    ( k2_relset_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)),k2_funct_1(k2_funct_1(X1))) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_293,plain,
    ( k2_relset_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)),k2_funct_1(k2_funct_1(X1))) = k2_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_294,plain,
    ( r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_295,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1))) = k2_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_296,plain,
    ( k2_relset_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))),k2_funct_1(k2_funct_1(X1))) = k2_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_297,plain,
    ( r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_298,plain,
    ( r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_299,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X3 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_94]),
    [final]).

cnf(c_0_300,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_126]),
    [final]).

cnf(c_0_301,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_126]),
    [final]).

cnf(c_0_302,plain,
    ( r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_303,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))
    | ~ v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_94]),
    [final]).

cnf(c_0_304,plain,
    ( r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_305,plain,
    ( r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_306,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_307,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1))) = k2_relat_1(X1)
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_308,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X3 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)
    | r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_78]),
    [final]).

cnf(c_0_309,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_122]),
    [final]).

cnf(c_0_310,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_311,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_312,plain,
    ( k2_relset_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1))) = k2_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_313,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_186]),
    [final]).

cnf(c_0_314,plain,
    ( k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3)) = k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))
    | X3 = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_162]),
    [final]).

cnf(c_0_315,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_123]),
    [final]).

cnf(c_0_316,plain,
    ( r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_317,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_318,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)
    | v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_81]),
    [final]).

cnf(c_0_319,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)
    | v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_81]),
    [final]).

cnf(c_0_320,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_321,plain,
    ( r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1)))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_322,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))
    | m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_94]),
    [final]).

cnf(c_0_323,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_189]),
    [final]).

cnf(c_0_324,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_124]),
    [final]).

cnf(c_0_325,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_326,plain,
    ( k2_relset_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1))) = k2_relat_1(X1)
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_327,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_99]),
    [final]).

cnf(c_0_328,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2)
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_122]),
    [final]).

cnf(c_0_329,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_190]),
    [final]).

cnf(c_0_330,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))
    | ~ r1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_190]),
    [final]).

cnf(c_0_331,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_122]),
    [final]).

cnf(c_0_332,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_333,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_123]),
    [final]).

cnf(c_0_334,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_335,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_69]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_336,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_125]),
    [final]).

cnf(c_0_337,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(X1)),k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_338,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_124]),
    [final]).

cnf(c_0_339,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_124]),
    [final]).

cnf(c_0_340,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_125]),
    [final]).

cnf(c_0_341,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_125]),
    [final]).

cnf(c_0_342,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_123]),
    [final]).

cnf(c_0_343,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(X3)
    | v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_126]),
    [final]).

cnf(c_0_344,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_xboole_0(k2_funct_1(esk6_0))
    | ~ v2_funct_1(esk6_0)
    | ~ r1_xboole_0(k2_funct_1(esk6_0),k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_345,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_193]),
    [final]).

cnf(c_0_346,plain,
    ( v5_relat_1(k2_funct_1(k2_funct_1(X1)),k2_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_67]),c_0_100]),c_0_85]),
    [final]).

cnf(c_0_347,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_195]),
    [final]).

cnf(c_0_348,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_xboole_0(k2_funct_1(esk6_0))
    | ~ v2_funct_1(esk6_0)
    | ~ r1_xboole_0(k2_funct_1(esk6_0),k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_349,negated_conjecture,
    ( k2_relset_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0),k2_funct_1(esk6_0)) = k2_relat_1(k2_funct_1(esk6_0))
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_350,plain,
    ( v1_partfun1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_196]),c_0_100]),
    [final]).

cnf(c_0_351,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X3 = k1_xboole_0
    | v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)
    | r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)
    | ~ v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_58]),
    [final]).

cnf(c_0_352,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_353,negated_conjecture,
    ( k2_relset_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0),k2_funct_1(esk6_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_354,negated_conjecture,
    ( k2_relset_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0),k2_funct_1(esk6_0)) = k2_relat_1(k2_funct_1(esk6_0))
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_355,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | r2_hidden(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_356,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | r2_hidden(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_357,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk6_0),k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_358,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | r1_tarski(k2_funct_1(esk6_0),k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0)))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_359,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | r1_tarski(k2_funct_1(esk6_0),k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0)))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_360,plain,
    ( v5_relat_1(k2_funct_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_178]),
    [final]).

cnf(c_0_361,negated_conjecture,
    ( k2_relset_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0),k2_funct_1(esk6_0)) = u1_struct_0(esk4_0)
    | u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_362,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_relat_1(k2_funct_1(esk6_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_91]),c_0_55]),c_0_75])]),
    [final]).

cnf(c_0_363,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_124]),
    [final]).

cnf(c_0_364,plain,
    ( esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_125]),
    [final]).

cnf(c_0_365,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 = k1_xboole_0
    | v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)
    | ~ v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)
    | ~ v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_129]),
    [final]).

cnf(c_0_366,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_97]),
    [final]).

cnf(c_0_367,plain,
    ( X1 = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))
    | ~ r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_133]),
    [final]).

cnf(c_0_368,plain,
    ( X1 = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(esk1_2(k1_xboole_0,X1))
    | ~ r1_tarski(esk1_2(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_187,c_0_79]),
    [final]).

cnf(c_0_369,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))))
    | ~ v2_funct_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_145]),c_0_55])]),c_0_115]),c_0_146]),
    [final]).

cnf(c_0_370,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),X1)))
    | ~ v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_197]),c_0_116])])]),
    [final]).

cnf(c_0_371,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X1)
    | r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_198]),
    [final]).

cnf(c_0_372,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_orders_2(esk3_1(X1)))
    | ~ l1_orders_2(X1)
    | ~ r1_xboole_0(u1_orders_2(esk3_1(X1)),u1_orders_2(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_199]),
    [final]).

cnf(c_0_373,plain,
    ( esk1_2(k1_xboole_0,X1) = k1_xboole_0
    | X1 = k1_zfmisc_1(k1_xboole_0)
    | ~ r1_tarski(esk1_2(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_187,c_0_80]),
    [final]).

cnf(c_0_374,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk3_1(X1)))
    | ~ l1_orders_2(X1)
    | ~ r1_xboole_0(u1_struct_0(esk3_1(X1)),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_200]),
    [final]).

cnf(c_0_375,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk6_0),k2_relat_1(esk6_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_145]),c_0_55])]),c_0_115]),c_0_146]),
    [final]).

cnf(c_0_376,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X1)
    | ~ v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_197]),c_0_116])])]),
    [final]).

cnf(c_0_377,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | ~ v2_funct_1(esk6_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_91]),c_0_202]),
    [final]).

cnf(c_0_378,plain,
    ( X1 = k1_xboole_0
    | v1_xboole_0(esk2_1(k1_zfmisc_1(X1)))
    | ~ r1_xboole_0(esk2_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_101]),
    [final]).

cnf(c_0_379,plain,
    ( v2_struct_0(X1)
    | r2_hidden(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_199]),
    [final]).

cnf(c_0_380,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_197]),c_0_116])])]),
    [final]).

cnf(c_0_381,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v5_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_129]),
    [final]).

cnf(c_0_382,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v4_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_129]),
    [final]).

cnf(c_0_383,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_199]),
    [final]).

cnf(c_0_384,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v1_xboole_0(esk6_0)
    | ~ r1_xboole_0(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_203]),
    [final]).

cnf(c_0_385,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(k1_xboole_0,X2)
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_116]),
    [final]).

cnf(c_0_386,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | v1_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_129]),
    [final]).

cnf(c_0_387,plain,
    ( v2_struct_0(X1)
    | r2_hidden(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_200]),
    [final]).

cnf(c_0_388,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_101]),
    [final]).

cnf(c_0_389,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ r1_xboole_0(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_204]),
    [final]).

cnf(c_0_390,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_200]),
    [final]).

cnf(c_0_391,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_203]),
    [final]).

cnf(c_0_392,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    | k2_relat_1(esk6_0) != u1_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_205]),c_0_54]),c_0_55]),c_0_53])]),
    [final]).

cnf(c_0_393,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    | k2_relat_1(esk6_0) != u1_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_205]),c_0_54]),c_0_55]),c_0_53])]),
    [final]).

cnf(c_0_394,negated_conjecture,
    ( u1_struct_0(esk5_0) = k1_xboole_0
    | v5_relat_1(esk6_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_115]),
    [final]).

cnf(c_0_395,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_47]),
    [final]).

cnf(c_0_396,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0))
    | k2_relat_1(esk6_0) != u1_struct_0(esk5_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_205]),c_0_54]),c_0_55]),c_0_53])]),
    [final]).

cnf(c_0_397,plain,
    ( l1_orders_2(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_142]),
    [final]).

cnf(c_0_398,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89]),
    [final]).

cnf(c_0_399,plain,
    ( v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_206]),
    [final]).

cnf(c_0_400,plain,
    ( v4_yellow_0(esk3_1(X1),X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112]),
    [final]).

cnf(c_0_401,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | esk2_1(X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_402,plain,
    ( v1_orders_2(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112]),
    [final]).

cnf(c_0_403,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_207]),
    [final]).

cnf(c_0_404,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk3_1(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112]),
    [final]).

cnf(c_0_405,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_208]),
    [final]).

cnf(c_0_406,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_407,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_408,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_209,c_0_60]),
    [final]).

cnf(c_0_409,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_204]),
    [final]).

cnf(c_0_410,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_210]),c_0_211])]),
    [final]).

cnf(c_0_411,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_148]),
    [final]).

cnf(c_0_412,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_116]),
    [final]).

cnf(c_0_413,negated_conjecture,
    ( v5_relat_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_53]),
    [final]).

cnf(c_0_414,negated_conjecture,
    ( v23_waybel_0(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_415,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_416,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.20/0.44  # and selection function SelectNewComplexAHPNS.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.030 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # No proof found!
% 0.20/0.44  # SZS status CounterSatisfiable
% 0.20/0.44  # SZS output start Saturation
% 0.20/0.44  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.44  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.20/0.44  fof(t67_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_waybel_0)).
% 0.20/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.44  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.20/0.44  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.20/0.44  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.20/0.44  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.44  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.44  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.44  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.44  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.44  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.44  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.44  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.20/0.44  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.44  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.20/0.44  fof(dt_m1_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 0.20/0.44  fof(rc4_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>?[X2]:(((m1_yellow_0(X2,X1)&~(v2_struct_0(X2)))&v1_orders_2(X2))&v4_yellow_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_yellow_0)).
% 0.20/0.44  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.44  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.44  fof(c_0_22, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|r1_tarski(X9,X7)|X8!=k1_zfmisc_1(X7))&(~r1_tarski(X10,X7)|r2_hidden(X10,X8)|X8!=k1_zfmisc_1(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|~r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11))&(r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.44  fof(c_0_23, plain, ![X31, X32, X33]:((X32=k1_xboole_0|v1_partfun1(X33,X31)|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(X31!=k1_xboole_0|v1_partfun1(X33,X31)|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.20/0.44  fof(c_0_24, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t67_waybel_0])).
% 0.20/0.44  fof(c_0_25, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.44  fof(c_0_26, plain, ![X5, X6]:(v1_xboole_0(X6)|(~r1_tarski(X6,X5)|~r1_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.20/0.44  fof(c_0_27, plain, ![X40, X41, X42]:((X41=k1_xboole_0|~r2_hidden(X41,X40)|k3_tarski(X40)!=k1_xboole_0)&((esk2_1(X42)!=k1_xboole_0|k3_tarski(X42)=k1_xboole_0)&(r2_hidden(esk2_1(X42),X42)|k3_tarski(X42)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.20/0.44  fof(c_0_28, plain, ![X14]:k3_tarski(k1_zfmisc_1(X14))=X14, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.20/0.44  cnf(c_0_29, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.44  fof(c_0_30, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.44  fof(c_0_31, plain, ![X37]:(((v1_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(v1_funct_2(X37,k1_relat_1(X37),k2_relat_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X37),k2_relat_1(X37))))|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.44  fof(c_0_32, plain, ![X29, X30]:((~v1_partfun1(X30,X29)|k1_relat_1(X30)=X29|(~v1_relat_1(X30)|~v4_relat_1(X30,X29)))&(k1_relat_1(X30)!=X29|v1_partfun1(X30,X29)|(~v1_relat_1(X30)|~v4_relat_1(X30,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.44  fof(c_0_33, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.44  cnf(c_0_34, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  fof(c_0_35, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_orders_2(esk4_0))&((~v2_struct_0(esk5_0)&l1_orders_2(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(v23_waybel_0(esk6_0,esk4_0,esk5_0)&(~v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|k2_relat_1(k2_funct_1(esk6_0))!=u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.20/0.44  fof(c_0_36, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.44  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.44  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.20/0.44  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_tarski(esk1_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.20/0.44  cnf(c_0_40, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.44  fof(c_0_41, plain, ![X4]:r1_xboole_0(X4,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.44  cnf(c_0_42, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.44  cnf(c_0_43, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.20/0.44  cnf(c_0_44, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.44  fof(c_0_45, plain, ![X34, X35, X36]:(((v1_funct_1(k2_funct_1(X36))|(~v2_funct_1(X36)|k2_relset_1(X34,X35,X36)!=X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(v1_funct_2(k2_funct_1(X36),X35,X34)|(~v2_funct_1(X36)|k2_relset_1(X34,X35,X36)!=X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&(m1_subset_1(k2_funct_1(X36),k1_zfmisc_1(k2_zfmisc_1(X35,X34)))|(~v2_funct_1(X36)|k2_relset_1(X34,X35,X36)!=X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.44  cnf(c_0_46, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.20/0.44  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.20/0.44  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.20/0.44  fof(c_0_49, plain, ![X19]:((k2_relat_1(X19)=k1_relat_1(k2_funct_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k1_relat_1(X19)=k2_relat_1(k2_funct_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.44  cnf(c_0_50, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.44  cnf(c_0_52, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_34]), ['final']).
% 0.20/0.44  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.44  cnf(c_0_54, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.44  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.44  cnf(c_0_56, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.44  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_37]), ['final']).
% 0.20/0.44  cnf(c_0_58, plain, (X1=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,X1),k1_zfmisc_1(X2))|r2_hidden(esk1_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['final']).
% 0.20/0.44  cnf(c_0_59, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),X1)|v1_xboole_0(esk1_2(X2,X1))|~r1_xboole_0(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_40, c_0_39]), ['final']).
% 0.20/0.44  cnf(c_0_60, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.20/0.44  cnf(c_0_61, plain, (X1=k1_xboole_0|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43])]), ['final']).
% 0.20/0.44  cnf(c_0_62, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,X1),k1_zfmisc_1(X2))|r2_hidden(esk1_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_44, c_0_39]), ['final']).
% 0.20/0.44  cnf(c_0_63, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.20/0.44  cnf(c_0_64, plain, (k2_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1)=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47]), ['final']).
% 0.20/0.44  cnf(c_0_65, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.20/0.44  cnf(c_0_66, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_47]), ['final']).
% 0.20/0.44  cnf(c_0_67, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.44  cnf(c_0_68, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.20/0.44  cnf(c_0_69, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.44  cnf(c_0_70, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_50]), ['final']).
% 0.20/0.44  cnf(c_0_71, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_47]), ['final']).
% 0.20/0.44  cnf(c_0_72, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.20/0.44  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_partfun1(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])]), ['final']).
% 0.20/0.44  cnf(c_0_74, negated_conjecture, (v4_relat_1(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_53]), ['final']).
% 0.20/0.44  cnf(c_0_75, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_53]), ['final']).
% 0.20/0.44  fof(c_0_76, plain, ![X16]:m1_subset_1(k1_subset_1(X16),k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.20/0.44  fof(c_0_77, plain, ![X15]:k1_subset_1(X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.44  cnf(c_0_78, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['final']).
% 0.20/0.44  cnf(c_0_79, plain, (X1=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,X1),X1)|v1_xboole_0(esk1_2(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_59, c_0_60]), ['final']).
% 0.20/0.44  cnf(c_0_80, plain, (esk1_2(k1_xboole_0,X1)=k1_xboole_0|X1=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62]), ['final']).
% 0.20/0.44  cnf(c_0_81, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_39]), ['final']).
% 0.20/0.44  cnf(c_0_82, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_47]), c_0_65]), ['final']).
% 0.20/0.44  cnf(c_0_83, plain, (r2_hidden(esk2_1(X1),X1)|k3_tarski(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.44  cnf(c_0_84, plain, (r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.44  cnf(c_0_85, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_64]), c_0_47]), c_0_65]), ['final']).
% 0.20/0.44  cnf(c_0_86, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 0.20/0.44  cnf(c_0_87, plain, (r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_66]), ['final']).
% 0.20/0.44  cnf(c_0_88, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71]), ['final']).
% 0.20/0.44  fof(c_0_89, plain, ![X44, X45]:(((r1_tarski(u1_struct_0(X45),u1_struct_0(X44))|~m1_yellow_0(X45,X44)|~l1_orders_2(X45)|~l1_orders_2(X44))&(r1_tarski(u1_orders_2(X45),u1_orders_2(X44))|~m1_yellow_0(X45,X44)|~l1_orders_2(X45)|~l1_orders_2(X44)))&(~r1_tarski(u1_struct_0(X45),u1_struct_0(X44))|~r1_tarski(u1_orders_2(X45),u1_orders_2(X44))|m1_yellow_0(X45,X44)|~l1_orders_2(X45)|~l1_orders_2(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.20/0.44  fof(c_0_90, plain, ![X46, X47]:(~l1_orders_2(X46)|(~m1_yellow_0(X47,X46)|l1_orders_2(X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (k1_relat_1(esk6_0)=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75])]), ['final']).
% 0.20/0.44  cnf(c_0_92, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.44  cnf(c_0_93, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.44  cnf(c_0_94, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_78]), ['final']).
% 0.20/0.44  cnf(c_0_95, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.44  cnf(c_0_96, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_78]), ['final']).
% 0.20/0.44  cnf(c_0_97, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_79]), ['final']).
% 0.20/0.44  cnf(c_0_98, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=k1_xboole_0|k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|r1_tarski(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_80]), ['final']).
% 0.20/0.44  cnf(c_0_99, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)), inference(spm,[status(thm)],[c_0_38, c_0_81]), ['final']).
% 0.20/0.44  cnf(c_0_100, plain, (v1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_82]), ['final']).
% 0.20/0.44  cnf(c_0_101, plain, (X1=k1_xboole_0|r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_83]), c_0_43]), ['final']).
% 0.20/0.44  cnf(c_0_102, plain, (r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.44  cnf(c_0_103, plain, (k2_relset_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)),k2_funct_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_67])).
% 0.20/0.44  cnf(c_0_104, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_67])).
% 0.20/0.44  cnf(c_0_105, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_67])).
% 0.20/0.44  cnf(c_0_106, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_86, c_0_85])).
% 0.20/0.44  cnf(c_0_107, plain, (r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_67])).
% 0.20/0.44  cnf(c_0_108, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_69])).
% 0.20/0.44  cnf(c_0_109, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_88, c_0_67])).
% 0.20/0.44  cnf(c_0_110, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.44  cnf(c_0_111, plain, (l1_orders_2(X2)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_90]), ['final']).
% 0.20/0.44  fof(c_0_112, plain, ![X48]:((((m1_yellow_0(esk3_1(X48),X48)|(v2_struct_0(X48)|~l1_orders_2(X48)))&(~v2_struct_0(esk3_1(X48))|(v2_struct_0(X48)|~l1_orders_2(X48))))&(v1_orders_2(esk3_1(X48))|(v2_struct_0(X48)|~l1_orders_2(X48))))&(v4_yellow_0(esk3_1(X48),X48)|(v2_struct_0(X48)|~l1_orders_2(X48)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_yellow_0])])])])])).
% 0.20/0.44  cnf(c_0_113, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.44  cnf(c_0_114, negated_conjecture, (~v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|k2_relat_1(k2_funct_1(esk6_0))!=u1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.44  cnf(c_0_115, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.44  cnf(c_0_116, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_92, c_0_93]), ['final']).
% 0.20/0.44  cnf(c_0_117, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_46, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_118, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_119, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_120, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_95, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_121, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_51, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_122, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_96, c_0_60]), ['final']).
% 0.20/0.44  cnf(c_0_123, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_97]), ['final']).
% 0.20/0.44  cnf(c_0_124, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(X1))=k1_xboole_0|k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_98]), ['final']).
% 0.20/0.44  cnf(c_0_125, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|m1_subset_1(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_58]), ['final']).
% 0.20/0.44  cnf(c_0_126, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_44, c_0_99]), ['final']).
% 0.20/0.44  cnf(c_0_127, plain, (k2_relset_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1),k2_funct_1(X1))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.44  cnf(c_0_128, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.20/0.44  cnf(c_0_129, plain, (X1=k1_xboole_0|m1_subset_1(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_101]), ['final']).
% 0.20/0.44  cnf(c_0_130, plain, (r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_131, plain, (r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_82]), ['final']).
% 0.20/0.44  cnf(c_0_132, plain, (v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_66]), ['final']).
% 0.20/0.44  cnf(c_0_133, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_56, c_0_58]), ['final']).
% 0.20/0.44  cnf(c_0_134, plain, (k2_relset_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)),k2_funct_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_103, c_0_85])).
% 0.20/0.44  cnf(c_0_135, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_104, c_0_85])).
% 0.20/0.44  cnf(c_0_136, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_105, c_0_85])).
% 0.20/0.44  cnf(c_0_137, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_106, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_138, plain, (r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_107, c_0_85])).
% 0.20/0.44  cnf(c_0_139, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_108, c_0_85])).
% 0.20/0.44  cnf(c_0_140, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_109, c_0_85])).
% 0.20/0.44  cnf(c_0_141, plain, (r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_110, c_0_111]), ['final']).
% 0.20/0.44  cnf(c_0_142, plain, (m1_yellow_0(esk3_1(X1),X1)|v2_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_112]), ['final']).
% 0.20/0.44  cnf(c_0_143, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_113, c_0_111]), ['final']).
% 0.20/0.44  cnf(c_0_144, negated_conjecture, (k1_relat_1(esk6_0)!=u1_struct_0(esk4_0)|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)|~v1_funct_1(k2_funct_1(esk6_0))|~v1_relat_1(esk6_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_69]), c_0_55])])).
% 0.20/0.44  cnf(c_0_145, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0),esk6_0)=k2_relat_1(esk6_0)|u1_struct_0(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_115]), ['final']).
% 0.20/0.44  cnf(c_0_146, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_funct_2(esk6_0,u1_struct_0(esk4_0),k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.44  cnf(c_0_147, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_148, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_116]), ['final']).
% 0.20/0.44  cnf(c_0_149, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relset_1(X3,X4,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_46, c_0_117]), ['final']).
% 0.20/0.44  cnf(c_0_150, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_46, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_151, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)), inference(spm,[status(thm)],[c_0_46, c_0_118]), ['final']).
% 0.20/0.44  cnf(c_0_152, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_46, c_0_119]), ['final']).
% 0.20/0.44  cnf(c_0_153, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_46, c_0_120]), ['final']).
% 0.20/0.44  cnf(c_0_154, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)), inference(spm,[status(thm)],[c_0_46, c_0_121]), ['final']).
% 0.20/0.44  cnf(c_0_155, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_46, c_0_122]), ['final']).
% 0.20/0.44  cnf(c_0_156, plain, (k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_46, c_0_123]), ['final']).
% 0.20/0.44  cnf(c_0_157, plain, (k2_relset_1(X1,X2,esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_124]), ['final']).
% 0.20/0.44  cnf(c_0_158, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_125]), ['final']).
% 0.20/0.44  cnf(c_0_159, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_46, c_0_126]), ['final']).
% 0.20/0.44  cnf(c_0_160, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_46, c_0_99]), ['final']).
% 0.20/0.44  cnf(c_0_161, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)), inference(spm,[status(thm)],[c_0_46, c_0_78]), ['final']).
% 0.20/0.44  cnf(c_0_162, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),X3),X3)), inference(spm,[status(thm)],[c_0_46, c_0_58]), ['final']).
% 0.20/0.44  cnf(c_0_163, plain, (k2_relset_1(k2_relat_1(X1),k1_relat_1(X1),k2_funct_1(X1))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_127, c_0_67]), ['final']).
% 0.20/0.44  cnf(c_0_164, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_64]), c_0_47]), c_0_65]), ['final']).
% 0.20/0.44  cnf(c_0_165, plain, (k2_relset_1(X1,X2,esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_zfmisc_1(X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_129]), ['final']).
% 0.20/0.44  cnf(c_0_166, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)), inference(spm,[status(thm)],[c_0_95, c_0_120]), ['final']).
% 0.20/0.44  cnf(c_0_167, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_95, c_0_99]), ['final']).
% 0.20/0.44  cnf(c_0_168, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_51, c_0_121]), ['final']).
% 0.20/0.44  cnf(c_0_169, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_51, c_0_99]), ['final']).
% 0.20/0.44  cnf(c_0_170, plain, (v1_xboole_0(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))), inference(spm,[status(thm)],[c_0_40, c_0_130]), ['final']).
% 0.20/0.44  cnf(c_0_171, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_95, c_0_78]), ['final']).
% 0.20/0.44  cnf(c_0_172, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_78]), ['final']).
% 0.20/0.44  cnf(c_0_173, plain, (v1_xboole_0(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(X1),k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_131]), ['final']).
% 0.20/0.44  cnf(c_0_174, plain, (v1_xboole_0(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(X1),k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.44  cnf(c_0_175, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_56, c_0_99]), ['final']).
% 0.20/0.44  cnf(c_0_176, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_133]), ['final']).
% 0.20/0.44  cnf(c_0_177, plain, (k2_relset_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)),k2_funct_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_134, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_178, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_135, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_179, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_136, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_180, plain, (k2_relset_1(k2_relat_1(X1),k1_relat_1(X1),k2_funct_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_82]), ['final']).
% 0.20/0.44  cnf(c_0_181, plain, (r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_131]), ['final']).
% 0.20/0.44  cnf(c_0_182, plain, (k2_relset_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1),k2_funct_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_137]), ['final']).
% 0.20/0.44  cnf(c_0_183, plain, (r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_138, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_184, plain, (r2_hidden(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.44  cnf(c_0_185, plain, (r1_tarski(k2_funct_1(X1),k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.44  cnf(c_0_186, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_62]), ['final']).
% 0.20/0.44  cnf(c_0_187, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk1_2(X1,X2),X2)|~r1_tarski(esk1_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.20/0.44  cnf(c_0_188, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_139, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_189, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_56, c_0_94]), ['final']).
% 0.20/0.44  cnf(c_0_190, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1)|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_48, c_0_122]), ['final']).
% 0.20/0.44  cnf(c_0_191, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_140, c_0_100]), ['final']).
% 0.20/0.44  cnf(c_0_192, plain, (v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_82]), ['final']).
% 0.20/0.44  cnf(c_0_193, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_95, c_0_58]), ['final']).
% 0.20/0.44  cnf(c_0_194, plain, (v5_relat_1(k2_funct_1(X1),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_95, c_0_82]), ['final']).
% 0.20/0.44  cnf(c_0_195, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_51, c_0_58]), ['final']).
% 0.20/0.44  cnf(c_0_196, plain, (v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_137]), ['final']).
% 0.20/0.44  cnf(c_0_197, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_116]), ['final']).
% 0.20/0.44  cnf(c_0_198, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r1_tarski(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_61, c_0_39]), ['final']).
% 0.20/0.44  cnf(c_0_199, plain, (v2_struct_0(X1)|r1_tarski(u1_orders_2(esk3_1(X1)),u1_orders_2(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_141, c_0_142]), ['final']).
% 0.20/0.44  cnf(c_0_200, plain, (v2_struct_0(X1)|r1_tarski(u1_struct_0(esk3_1(X1)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_143, c_0_142]), ['final']).
% 0.20/0.44  cnf(c_0_201, negated_conjecture, (k1_relat_1(esk6_0)!=u1_struct_0(esk4_0)|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)|~v1_funct_1(k2_funct_1(esk6_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_75])]), ['final']).
% 0.20/0.44  cnf(c_0_202, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_funct_1(k2_funct_1(esk6_0))|~v2_funct_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_145]), c_0_55])]), c_0_115]), c_0_146]), ['final']).
% 0.20/0.44  cnf(c_0_203, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))), inference(spm,[status(thm)],[c_0_48, c_0_115]), ['final']).
% 0.20/0.44  cnf(c_0_204, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_48, c_0_53]), ['final']).
% 0.20/0.44  cnf(c_0_205, negated_conjecture, (k2_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_53]), ['final']).
% 0.20/0.44  cnf(c_0_206, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[c_0_147])).
% 0.20/0.44  fof(c_0_207, plain, ![X38]:(v2_struct_0(X38)|~l1_struct_0(X38)|~v1_xboole_0(u1_struct_0(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.44  fof(c_0_208, plain, ![X39]:(~l1_orders_2(X39)|l1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.44  cnf(c_0_209, plain, (v1_xboole_0(k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_148])).
% 0.20/0.44  cnf(c_0_210, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_116]), ['final']).
% 0.20/0.44  cnf(c_0_211, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_116]), ['final']).
% 0.20/0.44  cnf(c_0_212, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_149]), c_0_150]), ['final']).
% 0.20/0.44  cnf(c_0_213, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_149]), c_0_117]), ['final']).
% 0.20/0.44  cnf(c_0_214, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))),X4,X3)|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_149]), c_0_150]), ['final']).
% 0.20/0.44  cnf(c_0_215, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_149]), c_0_117]), ['final']).
% 0.20/0.44  cnf(c_0_216, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_149]), c_0_150]), ['final']).
% 0.20/0.44  cnf(c_0_217, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_149]), c_0_117]), ['final']).
% 0.20/0.44  cnf(c_0_218, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_151]), c_0_118]), ['final']).
% 0.20/0.44  cnf(c_0_219, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_152]), c_0_119]), ['final']).
% 0.20/0.44  cnf(c_0_220, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_153]), c_0_120]), ['final']).
% 0.20/0.44  cnf(c_0_221, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_151]), c_0_118]), ['final']).
% 0.20/0.44  cnf(c_0_222, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_152]), c_0_119]), ['final']).
% 0.20/0.44  cnf(c_0_223, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_153]), c_0_120]), ['final']).
% 0.20/0.44  cnf(c_0_224, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_154]), c_0_121]), ['final']).
% 0.20/0.44  cnf(c_0_225, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X4,X3)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_154]), c_0_121]), ['final']).
% 0.20/0.44  cnf(c_0_226, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_151]), c_0_118]), ['final']).
% 0.20/0.44  cnf(c_0_227, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_152]), c_0_119]), ['final']).
% 0.20/0.44  cnf(c_0_228, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_153]), c_0_120]), ['final']).
% 0.20/0.44  cnf(c_0_229, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X4|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v2_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_154]), c_0_121]), ['final']).
% 0.20/0.44  cnf(c_0_230, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_155]), c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_231, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_156]), c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_232, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_157]), c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_233, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_158]), c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_234, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_155]), c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_235, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_156]), c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_236, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_157]), c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_237, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_157]), c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_238, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_159]), c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_239, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_160]), c_0_99]), ['final']).
% 0.20/0.45  cnf(c_0_240, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_161]), c_0_78]), ['final']).
% 0.20/0.45  cnf(c_0_241, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_150]), c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_242, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X2,X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_158]), c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_243, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_155]), c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_244, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|m1_subset_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_117]), c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_245, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_159]), c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_246, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_160]), c_0_99]), ['final']).
% 0.20/0.45  cnf(c_0_247, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_161]), c_0_78]), ['final']).
% 0.20/0.45  cnf(c_0_248, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))),X3,X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_150]), c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_249, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_2(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_117]), c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_250, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_159]), c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_251, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))))|k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))!=X2|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v2_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_158]), c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_252, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_funct_1(k2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k2_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_156]), c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_253, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_160]), c_0_99]), ['final']).
% 0.20/0.45  cnf(c_0_254, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_161]), c_0_78]), ['final']).
% 0.20/0.45  cnf(c_0_255, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1))))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_150]), c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_256, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_funct_1(k2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_117]), c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_257, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))|k1_zfmisc_1(k2_zfmisc_1(X3,X4))=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))))), inference(spm,[status(thm)],[c_0_52, c_0_150]), ['final']).
% 0.20/0.45  cnf(c_0_258, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_117]), ['final']).
% 0.20/0.45  cnf(c_0_259, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|m1_subset_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_162]), c_0_58]), ['final']).
% 0.20/0.45  cnf(c_0_260, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_118]), ['final']).
% 0.20/0.45  cnf(c_0_261, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_119]), ['final']).
% 0.20/0.45  cnf(c_0_262, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_120]), ['final']).
% 0.20/0.45  cnf(c_0_263, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|X4=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3,X4)|~v1_funct_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_121]), ['final']).
% 0.20/0.45  cnf(c_0_264, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_2(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)),X3,X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_162]), c_0_58]), ['final']).
% 0.20/0.45  cnf(c_0_265, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_52, c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_266, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_funct_1(k2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1)))|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|k2_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))!=X3|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v2_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_162]), c_0_58]), ['final']).
% 0.20/0.45  cnf(c_0_267, plain, (m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_163]), c_0_82]), c_0_85]), c_0_164]), ['final']).
% 0.20/0.45  cnf(c_0_268, plain, (k2_relset_1(X1,X2,esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=k2_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_40, c_0_160]), ['final']).
% 0.20/0.45  cnf(c_0_269, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|k1_zfmisc_1(X3)=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)))|~r1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X3)),X3)), inference(spm,[status(thm)],[c_0_40, c_0_161]), ['final']).
% 0.20/0.45  cnf(c_0_270, plain, (v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1),k2_relat_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_163]), c_0_82]), c_0_85]), c_0_164]), ['final']).
% 0.20/0.45  cnf(c_0_271, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_272, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|X2=k1_xboole_0|v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_273, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|m1_subset_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_165]), c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_274, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X2))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(ef,[status(thm)],[c_0_166]), ['final']).
% 0.20/0.45  cnf(c_0_275, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_51, c_0_120]), ['final']).
% 0.20/0.45  cnf(c_0_276, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v5_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X4)|v4_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_95, c_0_121]), ['final']).
% 0.20/0.45  cnf(c_0_277, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_40, c_0_167]), ['final']).
% 0.20/0.45  cnf(c_0_278, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X1,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(ef,[status(thm)],[c_0_168]), ['final']).
% 0.20/0.45  cnf(c_0_279, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_2(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X2,X1)|k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_165]), c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_280, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_40, c_0_169]), ['final']).
% 0.20/0.45  cnf(c_0_281, plain, (v1_xboole_0(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1)))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_282, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X3)|v1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_171]), ['final']).
% 0.20/0.45  cnf(c_0_283, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|v1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_172]), ['final']).
% 0.20/0.45  cnf(c_0_284, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_funct_1(k2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))|k2_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))!=X2|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v2_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_165]), c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_285, plain, (v1_xboole_0(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_286, plain, (v1_xboole_0(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_287, plain, (v1_xboole_0(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_288, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|v1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~r1_xboole_0(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_40, c_0_175]), ['final']).
% 0.20/0.45  cnf(c_0_289, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|v1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_176]), ['final']).
% 0.20/0.45  cnf(c_0_290, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|X2=k1_xboole_0|v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r1_tarski(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3)|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_99]), ['final']).
% 0.20/0.45  cnf(c_0_291, plain, (v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_177]), c_0_178]), c_0_85]), c_0_179]), ['final']).
% 0.20/0.45  cnf(c_0_292, plain, (k2_relset_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)),k2_funct_1(k2_funct_1(X1)))=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_293, plain, (k2_relset_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)),k2_funct_1(k2_funct_1(X1)))=k2_relat_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_294, plain, (r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_295, plain, (k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1)))=k2_relat_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_296, plain, (k2_relset_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))),k2_funct_1(k2_funct_1(X1)))=k2_relat_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_297, plain, (r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_298, plain, (r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_299, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|X3=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_52, c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_300, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v5_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_95, c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_301, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v4_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_51, c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_302, plain, (r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_303, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|X2=k1_xboole_0|v1_partfun1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|m1_subset_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))|~v1_funct_2(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_304, plain, (r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_305, plain, (r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_306, plain, (m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_307, plain, (k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1)))=k2_relat_1(X1)|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_308, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|X3=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2)|r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),X2,X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_52, c_0_78]), ['final']).
% 0.20/0.45  cnf(c_0_309, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_51, c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_310, plain, (m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_311, plain, (m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_312, plain, (k2_relset_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1)))=k2_relat_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_313, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r2_hidden(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X2))|v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_186]), ['final']).
% 0.20/0.45  cnf(c_0_314, plain, (k2_relset_1(X1,X2,esk1_2(k2_zfmisc_1(X1,X2),X3))=k2_relat_1(esk1_2(k2_zfmisc_1(X1,X2),X3))|X3=k1_zfmisc_1(k2_zfmisc_1(X1,X2))|~r1_tarski(esk1_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_187, c_0_162]), ['final']).
% 0.20/0.45  cnf(c_0_315, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_51, c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_316, plain, (r2_hidden(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_317, plain, (v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1),k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_318, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X1)|v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_81]), ['final']).
% 0.20/0.45  cnf(c_0_319, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|r1_tarski(esk1_2(X2,k1_zfmisc_1(X1)),X2)|v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_81]), ['final']).
% 0.20/0.45  cnf(c_0_320, plain, (v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(k2_funct_1(k2_funct_1(X1))),k2_relat_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_321, plain, (r1_tarski(k2_funct_1(k2_funct_1(X1)),k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1)))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_322, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)))|m1_subset_1(esk1_2(k2_zfmisc_1(X2,X3),k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_94]), ['final']).
% 0.20/0.45  cnf(c_0_323, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k2_zfmisc_1(X3,X4))|v1_relat_1(esk1_2(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_56, c_0_189]), ['final']).
% 0.20/0.45  cnf(c_0_324, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_325, plain, (v1_funct_2(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1),k2_relat_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_326, plain, (k2_relset_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1),k2_funct_1(k2_funct_1(X1)))=k2_relat_1(X1)|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_327, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|m1_subset_1(esk1_2(X2,k1_zfmisc_1(X1)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(X2,k1_zfmisc_1(X1)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_99]), ['final']).
% 0.20/0.45  cnf(c_0_328, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2)|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_95, c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_329, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_44, c_0_190]), ['final']).
% 0.20/0.45  cnf(c_0_330, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|v1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)))|~r1_xboole_0(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_190]), ['final']).
% 0.20/0.45  cnf(c_0_331, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))|v1_xboole_0(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_56, c_0_122]), ['final']).
% 0.20/0.45  cnf(c_0_332, plain, (m1_subset_1(k2_funct_1(k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_333, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_95, c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_334, plain, (v1_partfun1(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_335, plain, (v4_relat_1(k2_funct_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_69]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_336, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|X2=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1,X2)|~v1_funct_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_52, c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_337, plain, (v1_funct_2(k2_funct_1(k2_funct_1(X1)),k2_relat_1(k2_funct_1(X1)),k2_relat_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_338, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_95, c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_339, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_51, c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_340, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v5_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_95, c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_341, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v4_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_342, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_56, c_0_123]), ['final']).
% 0.20/0.45  cnf(c_0_343, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(X3)|v1_relat_1(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|r2_hidden(esk1_2(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_56, c_0_126]), ['final']).
% 0.20/0.45  cnf(c_0_344, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_xboole_0(k2_funct_1(esk6_0))|~v2_funct_1(esk6_0)|~r1_xboole_0(k2_funct_1(esk6_0),k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_345, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v5_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X3)|~r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_187, c_0_193]), ['final']).
% 0.20/0.45  cnf(c_0_346, plain, (v5_relat_1(k2_funct_1(k2_funct_1(X1)),k2_relat_1(X1))|~v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_67]), c_0_100]), c_0_85]), ['final']).
% 0.20/0.45  cnf(c_0_347, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v4_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|~r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_187, c_0_195]), ['final']).
% 0.20/0.45  cnf(c_0_348, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_xboole_0(k2_funct_1(esk6_0))|~v2_funct_1(esk6_0)|~r1_xboole_0(k2_funct_1(esk6_0),k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_349, negated_conjecture, (k2_relset_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0),k2_funct_1(esk6_0))=k2_relat_1(k2_funct_1(esk6_0))|u1_struct_0(esk5_0)=k1_xboole_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_350, plain, (v1_partfun1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_196]), c_0_100]), ['final']).
% 0.20/0.45  cnf(c_0_351, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|X3=k1_xboole_0|v1_partfun1(esk1_2(k2_zfmisc_1(X2,X3),X1),X2)|r2_hidden(esk1_2(k2_zfmisc_1(X2,X3),X1),X1)|~v1_funct_2(esk1_2(k2_zfmisc_1(X2,X3),X1),X2,X3)|~v1_funct_1(esk1_2(k2_zfmisc_1(X2,X3),X1))), inference(spm,[status(thm)],[c_0_52, c_0_58]), ['final']).
% 0.20/0.45  cnf(c_0_352, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_353, negated_conjecture, (k2_relset_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0),k2_funct_1(esk6_0))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_354, negated_conjecture, (k2_relset_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0),k2_funct_1(esk6_0))=k2_relat_1(k2_funct_1(esk6_0))|u1_struct_0(esk5_0)=k1_xboole_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_355, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|r2_hidden(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_356, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|r2_hidden(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_357, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk6_0),k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_358, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|r1_tarski(k2_funct_1(esk6_0),k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0)))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_359, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|r1_tarski(k2_funct_1(esk6_0),k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0)))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_360, plain, (v5_relat_1(k2_funct_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_95, c_0_178]), ['final']).
% 0.20/0.45  cnf(c_0_361, negated_conjecture, (k2_relset_1(k1_relat_1(k2_funct_1(esk6_0)),u1_struct_0(esk4_0),k2_funct_1(esk6_0))=u1_struct_0(esk4_0)|u1_struct_0(esk5_0)=k1_xboole_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_362, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_relat_1(k2_funct_1(esk6_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_91]), c_0_55]), c_0_75])]), ['final']).
% 0.20/0.45  cnf(c_0_363, plain, (esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_56, c_0_124]), ['final']).
% 0.20/0.45  cnf(c_0_364, plain, (esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|v1_relat_1(esk1_2(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_56, c_0_125]), ['final']).
% 0.20/0.45  cnf(c_0_365, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2=k1_xboole_0|v1_partfun1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)|~v1_funct_2(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1,X2)|~v1_funct_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_366, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)))|~r1_xboole_0(esk1_2(k1_xboole_0,k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_97]), ['final']).
% 0.20/0.45  cnf(c_0_367, plain, (X1=k1_zfmisc_1(k2_zfmisc_1(X2,X3))|v1_relat_1(esk1_2(k2_zfmisc_1(X2,X3),X1))|~r1_tarski(esk1_2(k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_187, c_0_133]), ['final']).
% 0.20/0.45  cnf(c_0_368, plain, (X1=k1_zfmisc_1(k1_xboole_0)|v1_xboole_0(esk1_2(k1_xboole_0,X1))|~r1_tarski(esk1_2(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_187, c_0_79]), ['final']).
% 0.20/0.45  cnf(c_0_369, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk6_0),u1_struct_0(esk4_0))))|~v2_funct_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_145]), c_0_55])]), c_0_115]), c_0_146]), ['final']).
% 0.20/0.45  cnf(c_0_370, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),X1)))|~v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_197]), c_0_116])])]), ['final']).
% 0.20/0.45  cnf(c_0_371, plain, (esk1_2(X1,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(X1)|r2_hidden(esk1_2(X1,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_198]), ['final']).
% 0.20/0.45  cnf(c_0_372, plain, (v2_struct_0(X1)|v1_xboole_0(u1_orders_2(esk3_1(X1)))|~l1_orders_2(X1)|~r1_xboole_0(u1_orders_2(esk3_1(X1)),u1_orders_2(X1))), inference(spm,[status(thm)],[c_0_40, c_0_199]), ['final']).
% 0.20/0.45  cnf(c_0_373, plain, (esk1_2(k1_xboole_0,X1)=k1_xboole_0|X1=k1_zfmisc_1(k1_xboole_0)|~r1_tarski(esk1_2(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_187, c_0_80]), ['final']).
% 0.20/0.45  cnf(c_0_374, plain, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk3_1(X1)))|~l1_orders_2(X1)|~r1_xboole_0(u1_struct_0(esk3_1(X1)),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_40, c_0_200]), ['final']).
% 0.20/0.45  cnf(c_0_375, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk6_0),k2_relat_1(esk6_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_145]), c_0_55])]), c_0_115]), c_0_146]), ['final']).
% 0.20/0.45  cnf(c_0_376, plain, (v1_funct_2(k2_funct_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X1)|~v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_197]), c_0_116])])]), ['final']).
% 0.20/0.45  cnf(c_0_377, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|~v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|~v2_funct_1(esk6_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_91]), c_0_202]), ['final']).
% 0.20/0.45  cnf(c_0_378, plain, (X1=k1_xboole_0|v1_xboole_0(esk2_1(k1_zfmisc_1(X1)))|~r1_xboole_0(esk2_1(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_101]), ['final']).
% 0.20/0.45  cnf(c_0_379, plain, (v2_struct_0(X1)|r2_hidden(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_44, c_0_199]), ['final']).
% 0.20/0.45  cnf(c_0_380, plain, (v1_funct_1(k2_funct_1(k1_xboole_0))|~v1_funct_2(k1_xboole_0,X1,k2_relat_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_197]), c_0_116])])]), ['final']).
% 0.20/0.45  cnf(c_0_381, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v5_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_95, c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_382, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v4_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_51, c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_383, plain, (v2_struct_0(X1)|m1_subset_1(u1_orders_2(esk3_1(X1)),k1_zfmisc_1(u1_orders_2(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_38, c_0_199]), ['final']).
% 0.20/0.45  cnf(c_0_384, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v1_xboole_0(esk6_0)|~r1_xboole_0(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0)))), inference(spm,[status(thm)],[c_0_40, c_0_203]), ['final']).
% 0.20/0.45  cnf(c_0_385, plain, (X1=k1_xboole_0|v1_partfun1(k1_xboole_0,X2)|~v1_funct_2(k1_xboole_0,X2,X1)|~v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_116]), ['final']).
% 0.20/0.45  cnf(c_0_386, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|v1_relat_1(esk2_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_56, c_0_129]), ['final']).
% 0.20/0.45  cnf(c_0_387, plain, (v2_struct_0(X1)|r2_hidden(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_44, c_0_200]), ['final']).
% 0.20/0.45  cnf(c_0_388, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_101]), ['final']).
% 0.20/0.45  cnf(c_0_389, negated_conjecture, (v1_xboole_0(esk6_0)|~r1_xboole_0(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_40, c_0_204]), ['final']).
% 0.20/0.45  cnf(c_0_390, plain, (v2_struct_0(X1)|m1_subset_1(u1_struct_0(esk3_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_38, c_0_200]), ['final']).
% 0.20/0.45  cnf(c_0_391, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),k2_relat_1(esk6_0))))), inference(spm,[status(thm)],[c_0_44, c_0_203]), ['final']).
% 0.20/0.45  cnf(c_0_392, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))|k2_relat_1(esk6_0)!=u1_struct_0(esk5_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_205]), c_0_54]), c_0_55]), c_0_53])]), ['final']).
% 0.20/0.45  cnf(c_0_393, negated_conjecture, (v1_funct_2(k2_funct_1(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0))|k2_relat_1(esk6_0)!=u1_struct_0(esk5_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_205]), c_0_54]), c_0_55]), c_0_53])]), ['final']).
% 0.20/0.45  cnf(c_0_394, negated_conjecture, (u1_struct_0(esk5_0)=k1_xboole_0|v5_relat_1(esk6_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_95, c_0_115]), ['final']).
% 0.20/0.45  cnf(c_0_395, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_95, c_0_47]), ['final']).
% 0.20/0.45  cnf(c_0_396, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))|k2_relat_1(esk6_0)!=u1_struct_0(esk5_0)|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_205]), c_0_54]), c_0_55]), c_0_53])]), ['final']).
% 0.20/0.45  cnf(c_0_397, plain, (l1_orders_2(esk3_1(X1))|v2_struct_0(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_111, c_0_142]), ['final']).
% 0.20/0.45  cnf(c_0_398, plain, (m1_yellow_0(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_89]), ['final']).
% 0.20/0.45  cnf(c_0_399, plain, (v1_partfun1(X1,k1_xboole_0)|~v1_funct_2(X1,k1_xboole_0,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_206]), ['final']).
% 0.20/0.45  cnf(c_0_400, plain, (v4_yellow_0(esk3_1(X1),X1)|v2_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_112]), ['final']).
% 0.20/0.45  cnf(c_0_401, plain, (k3_tarski(X1)=k1_xboole_0|esk2_1(X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.45  cnf(c_0_402, plain, (v1_orders_2(esk3_1(X1))|v2_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_112]), ['final']).
% 0.20/0.45  cnf(c_0_403, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_207]), ['final']).
% 0.20/0.45  cnf(c_0_404, plain, (v2_struct_0(X1)|~v2_struct_0(esk3_1(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_112]), ['final']).
% 0.20/0.45  cnf(c_0_405, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_208]), ['final']).
% 0.20/0.45  cnf(c_0_406, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.45  cnf(c_0_407, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.45  cnf(c_0_408, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_209, c_0_60]), ['final']).
% 0.20/0.45  cnf(c_0_409, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_44, c_0_204]), ['final']).
% 0.20/0.45  cnf(c_0_410, plain, (v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_210]), c_0_211])]), ['final']).
% 0.20/0.45  cnf(c_0_411, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_148]), ['final']).
% 0.20/0.45  cnf(c_0_412, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_95, c_0_116]), ['final']).
% 0.20/0.45  cnf(c_0_413, negated_conjecture, (v5_relat_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_95, c_0_53]), ['final']).
% 0.20/0.45  cnf(c_0_414, negated_conjecture, (v23_waybel_0(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.45  cnf(c_0_415, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.45  cnf(c_0_416, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.20/0.45  # SZS output end Saturation
% 0.20/0.45  # Proof object total steps             : 417
% 0.20/0.45  # Proof object clause steps            : 372
% 0.20/0.45  # Proof object formula steps           : 45
% 0.20/0.45  # Proof object conjectures             : 50
% 0.20/0.45  # Proof object clause conjectures      : 47
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 48
% 0.20/0.45  # Proof object initial formulas used   : 22
% 0.20/0.45  # Proof object generating inferences   : 314
% 0.20/0.45  # Proof object simplifying inferences  : 237
% 0.20/0.45  # Parsed axioms                        : 22
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 49
% 0.20/0.45  # Removed in clause preprocessing      : 2
% 0.20/0.45  # Initial clauses in saturation        : 47
% 0.20/0.45  # Processed clauses                    : 633
% 0.20/0.45  # ...of these trivial                  : 0
% 0.20/0.45  # ...subsumed                          : 214
% 0.20/0.45  # ...remaining for further processing  : 419
% 0.20/0.45  # Other redundant clauses eliminated   : 8
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 22
% 0.20/0.45  # Backward-rewritten                   : 2
% 0.20/0.45  # Generated clauses                    : 562
% 0.20/0.45  # ...of the previous two non-trivial   : 541
% 0.20/0.45  # Contextual simplify-reflections      : 144
% 0.20/0.45  # Paramodulations                      : 542
% 0.20/0.45  # Factorizations                       : 12
% 0.20/0.45  # Equation resolutions                 : 8
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 344
% 0.20/0.45  #    Positive orientable unit clauses  : 23
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 2
% 0.20/0.45  #    Non-unit-clauses                  : 319
% 0.20/0.45  # Current number of unprocessed clauses: 0
% 0.20/0.45  # ...number of literals in the above   : 0
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 72
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 57554
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 3463
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 380
% 0.20/0.45  # Unit Clause-clause subsumption calls : 206
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 6
% 0.20/0.45  # BW rewrite match successes           : 2
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 25742
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.096 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.103 s
% 0.20/0.45  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
