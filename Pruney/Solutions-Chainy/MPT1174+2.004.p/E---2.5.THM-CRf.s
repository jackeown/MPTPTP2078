%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:02 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 618 expanded)
%              Number of clauses        :   44 ( 201 expanded)
%              Number of leaves         :   10 ( 149 expanded)
%              Depth                    :   14
%              Number of atoms          :  378 (4555 expanded)
%              Number of equality atoms :   19 ( 758 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X3)
                 => ( X2 = k1_funct_1(X3,u1_struct_0(X1))
                   => k3_orders_2(X1,X4,X2) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

fof(dt_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_orders_2(X3,X1,X2)
         => ( v6_orders_2(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(t80_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))
                 => ! [X5] :
                      ( m2_orders_2(X5,X1,X4)
                     => ( ( r2_hidden(X2,X5)
                          & X3 = k1_funct_1(X4,u1_struct_0(X1)) )
                       => r3_orders_2(X1,X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(t32_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( ( r2_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                      | ( r1_orders_2(X1,X2,X3)
                        & r2_orders_2(X1,X3,X4) ) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m2_orders_2(X4,X1,X3)
                   => ( X2 = k1_funct_1(X3,u1_struct_0(X1))
                     => k3_orders_2(X1,X4,X2) = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_orders_2])).

fof(c_0_11,plain,(
    ! [X24,X25,X26] :
      ( ( v6_orders_2(X26,X24)
        | ~ m2_orders_2(X26,X24,X25)
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_orders_1(X25,k1_orders_1(u1_struct_0(X24))) )
      & ( m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m2_orders_2(X26,X24,X25)
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_orders_1(X25,k1_orders_1(u1_struct_0(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))
    & m2_orders_2(esk5_0,esk2_0,esk4_0)
    & esk3_0 = k1_funct_1(esk4_0,u1_struct_0(esk2_0))
    & k3_orders_2(esk2_0,esk5_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v3_orders_2(X21)
      | ~ v4_orders_2(X21)
      | ~ v5_orders_2(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | m1_subset_1(k3_orders_2(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m2_orders_2(X1,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m2_orders_2(esk5_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_orders_2(X34,X35,X36)
        | ~ r2_hidden(X35,k3_orders_2(X34,X37,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( r2_hidden(X35,X37)
        | ~ r2_hidden(X35,k3_orders_2(X34,X37,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( ~ r2_orders_2(X34,X35,X36)
        | ~ r2_hidden(X35,X37)
        | r2_hidden(X35,k3_orders_2(X34,X37,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X11,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(esk1_1(X11),X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X14,X15)
        | ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X17,esk1_1(X11))
        | r1_xboole_0(X13,X11)
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k3_orders_2(esk2_0,esk5_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_36,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( v2_struct_0(X38)
      | ~ v3_orders_2(X38)
      | ~ v4_orders_2(X38)
      | ~ v5_orders_2(X38)
      | ~ l1_orders_2(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | ~ m1_orders_1(X41,k1_orders_1(u1_struct_0(X38)))
      | ~ m2_orders_2(X42,X38,X41)
      | ~ r2_hidden(X39,X42)
      | X40 != k1_funct_1(X41,u1_struct_0(X38))
      | r3_orders_2(X38,X40,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t80_orders_2])])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_39,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r3_orders_2(X27,X28,X29)
        | r1_orders_2(X27,X28,X29)
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27)) )
      & ( ~ r1_orders_2(X27,X28,X29)
        | r3_orders_2(X27,X28,X29)
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X5,X1,X4)
    | ~ r2_hidden(X2,X5)
    | X3 != k1_funct_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r3_orders_2(X1,k1_funct_1(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k1_funct_1(X2,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X4) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_47,plain,(
    ! [X18,X19,X20] :
      ( ( r1_orders_2(X18,X19,X20)
        | ~ r2_orders_2(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( X19 != X20
        | ~ r2_orders_2(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,X19,X20)
        | X19 = X20
        | r2_orders_2(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_48,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_orders_2(X30,X31,X32)
        | ~ r1_orders_2(X30,X32,X33)
        | r2_orders_2(X30,X31,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( ~ r1_orders_2(X30,X31,X32)
        | ~ r2_orders_2(X30,X32,X33)
        | r2_orders_2(X30,X31,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_orders_2])])])])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r3_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r3_orders_2(esk2_0,k1_funct_1(X1,u1_struct_0(esk2_0)),esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ m2_orders_2(X2,esk2_0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 = k1_funct_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_54,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r2_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))
    | ~ r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_24]),c_0_51]),c_0_15]),c_0_51]),c_0_22]),c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_59,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ r2_orders_2(esk2_0,X2,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_16]),c_0_17]),c_0_19])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_34]),c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_22]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_38]),c_0_22])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.64  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.47/0.64  # and selection function SelectNewComplexAHPNS.
% 0.47/0.64  #
% 0.47/0.64  # Preprocessing time       : 0.029 s
% 0.47/0.64  
% 0.47/0.64  # Proof found!
% 0.47/0.64  # SZS status Theorem
% 0.47/0.64  # SZS output start CNFRefutation
% 0.47/0.64  fof(t81_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))=>![X4]:(m2_orders_2(X4,X1,X3)=>(X2=k1_funct_1(X3,u1_struct_0(X1))=>k3_orders_2(X1,X4,X2)=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 0.47/0.64  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.47/0.64  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.47/0.64  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.47/0.64  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.47/0.64  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.47/0.64  fof(t80_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))=>![X5]:(m2_orders_2(X5,X1,X4)=>((r2_hidden(X2,X5)&X3=k1_funct_1(X4,u1_struct_0(X1)))=>r3_orders_2(X1,X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 0.47/0.64  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.47/0.64  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.47/0.64  fof(t32_orders_2, axiom, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))|(r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4)))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 0.47/0.64  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))=>![X4]:(m2_orders_2(X4,X1,X3)=>(X2=k1_funct_1(X3,u1_struct_0(X1))=>k3_orders_2(X1,X4,X2)=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t81_orders_2])).
% 0.47/0.64  fof(c_0_11, plain, ![X24, X25, X26]:((v6_orders_2(X26,X24)|~m2_orders_2(X26,X24,X25)|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_orders_1(X25,k1_orders_1(u1_struct_0(X24)))))&(m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|~m2_orders_2(X26,X24,X25)|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_orders_1(X25,k1_orders_1(u1_struct_0(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.47/0.64  fof(c_0_12, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk5_0,esk2_0,esk4_0)&(esk3_0=k1_funct_1(esk4_0,u1_struct_0(esk2_0))&k3_orders_2(esk2_0,esk5_0,esk3_0)!=k1_xboole_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.47/0.64  fof(c_0_13, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|m1_subset_1(k3_orders_2(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.47/0.64  cnf(c_0_14, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.64  cnf(c_0_15, negated_conjecture, (m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_21, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.64  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m2_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.47/0.64  cnf(c_0_24, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  fof(c_0_25, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.47/0.64  cnf(c_0_26, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.47/0.64  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.64  fof(c_0_28, plain, ![X34, X35, X36, X37]:(((r2_orders_2(X34,X35,X36)|~r2_hidden(X35,k3_orders_2(X34,X37,X36))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)))&(r2_hidden(X35,X37)|~r2_hidden(X35,k3_orders_2(X34,X37,X36))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34))))&(~r2_orders_2(X34,X35,X36)|~r2_hidden(X35,X37)|r2_hidden(X35,k3_orders_2(X34,X37,X36))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.47/0.64  cnf(c_0_29, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.64  cnf(c_0_30, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.47/0.64  fof(c_0_31, plain, ![X11, X13, X14, X15, X16, X17]:((r2_hidden(esk1_1(X11),X11)|X11=k1_xboole_0)&(~r2_hidden(X13,X14)|~r2_hidden(X14,X15)|~r2_hidden(X15,X16)|~r2_hidden(X16,X17)|~r2_hidden(X17,esk1_1(X11))|r1_xboole_0(X13,X11)|X11=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.47/0.64  cnf(c_0_32, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.64  cnf(c_0_33, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.64  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.64  cnf(c_0_35, negated_conjecture, (k3_orders_2(esk2_0,esk5_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  fof(c_0_36, plain, ![X38, X39, X40, X41, X42]:(v2_struct_0(X38)|~v3_orders_2(X38)|~v4_orders_2(X38)|~v5_orders_2(X38)|~l1_orders_2(X38)|(~m1_subset_1(X39,u1_struct_0(X38))|(~m1_subset_1(X40,u1_struct_0(X38))|(~m1_orders_1(X41,k1_orders_1(u1_struct_0(X38)))|(~m2_orders_2(X42,X38,X41)|(~r2_hidden(X39,X42)|X40!=k1_funct_1(X41,u1_struct_0(X38))|r3_orders_2(X38,X40,X39))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t80_orders_2])])])])).
% 0.47/0.64  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.47/0.64  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.47/0.64  fof(c_0_39, plain, ![X27, X28, X29]:((~r3_orders_2(X27,X28,X29)|r1_orders_2(X27,X28,X29)|(v2_struct_0(X27)|~v3_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))))&(~r1_orders_2(X27,X28,X29)|r3_orders_2(X27,X28,X29)|(v2_struct_0(X27)|~v3_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.47/0.64  cnf(c_0_40, plain, (v2_struct_0(X1)|r3_orders_2(X1,X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X5,X1,X4)|~r2_hidden(X2,X5)|X3!=k1_funct_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.64  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.47/0.64  cnf(c_0_42, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.64  cnf(c_0_43, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.64  cnf(c_0_44, plain, (r3_orders_2(X1,k1_funct_1(X2,u1_struct_0(X1)),X3)|v2_struct_0(X1)|~m2_orders_2(X4,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(k1_funct_1(X2,u1_struct_0(X1)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,X4)), inference(er,[status(thm)],[c_0_40])).
% 0.47/0.64  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.47/0.64  cnf(c_0_46, negated_conjecture, (r2_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.47/0.64  fof(c_0_47, plain, ![X18, X19, X20]:(((r1_orders_2(X18,X19,X20)|~r2_orders_2(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|~l1_orders_2(X18))&(X19!=X20|~r2_orders_2(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|~l1_orders_2(X18)))&(~r1_orders_2(X18,X19,X20)|X19=X20|r2_orders_2(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|~l1_orders_2(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.47/0.64  fof(c_0_48, plain, ![X30, X31, X32, X33]:((~r2_orders_2(X30,X31,X32)|~r1_orders_2(X30,X32,X33)|r2_orders_2(X30,X31,X33)|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|(~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)))&(~r1_orders_2(X30,X31,X32)|~r2_orders_2(X30,X32,X33)|r2_orders_2(X30,X31,X33)|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|(~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_orders_2])])])])).
% 0.47/0.64  cnf(c_0_49, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r3_orders_2(esk2_0,X1,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_38]), c_0_18]), c_0_19])]), c_0_20])).
% 0.47/0.64  cnf(c_0_50, negated_conjecture, (r3_orders_2(esk2_0,k1_funct_1(X1,u1_struct_0(esk2_0)),esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~m2_orders_2(X2,esk2_0,X1)|~m1_orders_1(X1,k1_orders_1(u1_struct_0(esk2_0)))|~m1_subset_1(k1_funct_1(X1,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.47/0.64  cnf(c_0_51, negated_conjecture, (esk3_0=k1_funct_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.64  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_35])).
% 0.47/0.64  cnf(c_0_53, negated_conjecture, (r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 0.47/0.64  cnf(c_0_54, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.47/0.64  cnf(c_0_55, plain, (r2_orders_2(X1,X2,X4)|~r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.64  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))|~r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_49, c_0_22])).
% 0.47/0.64  cnf(c_0_57, negated_conjecture, (r3_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_24]), c_0_51]), c_0_15]), c_0_51]), c_0_22]), c_0_52])])).
% 0.47/0.64  cnf(c_0_58, negated_conjecture, (r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)|~r2_hidden(esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_27])).
% 0.47/0.64  cnf(c_0_59, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_54])).
% 0.47/0.64  cnf(c_0_60, negated_conjecture, (r2_orders_2(esk2_0,X1,esk3_0)|~r1_orders_2(esk2_0,X1,X2)|~r2_orders_2(esk2_0,X2,esk3_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_16]), c_0_17]), c_0_19])])).
% 0.47/0.64  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.47/0.64  cnf(c_0_62, negated_conjecture, (r2_orders_2(esk2_0,esk1_1(k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_34]), c_0_35])).
% 0.47/0.64  cnf(c_0_63, negated_conjecture, (~r2_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_22]), c_0_19])])).
% 0.47/0.64  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_38]), c_0_22])]), c_0_63]), ['proof']).
% 0.47/0.64  # SZS output end CNFRefutation
% 0.47/0.64  # Proof object total steps             : 65
% 0.47/0.64  # Proof object clause steps            : 44
% 0.47/0.64  # Proof object formula steps           : 21
% 0.47/0.64  # Proof object conjectures             : 35
% 0.47/0.64  # Proof object clause conjectures      : 32
% 0.47/0.64  # Proof object formula conjectures     : 3
% 0.47/0.64  # Proof object initial clauses used    : 20
% 0.47/0.64  # Proof object initial formulas used   : 10
% 0.47/0.64  # Proof object generating inferences   : 21
% 0.47/0.64  # Proof object simplifying inferences  : 58
% 0.47/0.64  # Training examples: 0 positive, 0 negative
% 0.47/0.64  # Parsed axioms                        : 10
% 0.47/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.64  # Initial clauses                      : 27
% 0.47/0.64  # Removed in clause preprocessing      : 0
% 0.47/0.64  # Initial clauses in saturation        : 27
% 0.47/0.64  # Processed clauses                    : 1476
% 0.47/0.64  # ...of these trivial                  : 0
% 0.47/0.64  # ...subsumed                          : 71
% 0.47/0.64  # ...remaining for further processing  : 1405
% 0.47/0.64  # Other redundant clauses eliminated   : 2
% 0.47/0.64  # Clauses deleted for lack of memory   : 0
% 0.47/0.64  # Backward-subsumed                    : 15
% 0.47/0.64  # Backward-rewritten                   : 7
% 0.47/0.64  # Generated clauses                    : 9256
% 0.47/0.64  # ...of the previous two non-trivial   : 9237
% 0.47/0.64  # Contextual simplify-reflections      : 15
% 0.47/0.64  # Paramodulations                      : 9254
% 0.47/0.64  # Factorizations                       : 0
% 0.47/0.64  # Equation resolutions                 : 2
% 0.47/0.64  # Propositional unsat checks           : 0
% 0.47/0.64  #    Propositional check models        : 0
% 0.47/0.64  #    Propositional check unsatisfiable : 0
% 0.47/0.64  #    Propositional clauses             : 0
% 0.47/0.64  #    Propositional clauses after purity: 0
% 0.47/0.64  #    Propositional unsat core size     : 0
% 0.47/0.64  #    Propositional preprocessing time  : 0.000
% 0.47/0.64  #    Propositional encoding time       : 0.000
% 0.47/0.64  #    Propositional solver time         : 0.000
% 0.47/0.64  #    Success case prop preproc time    : 0.000
% 0.47/0.64  #    Success case prop encoding time   : 0.000
% 0.47/0.64  #    Success case prop solver time     : 0.000
% 0.47/0.64  # Current number of processed clauses  : 1381
% 0.47/0.64  #    Positive orientable unit clauses  : 77
% 0.47/0.64  #    Positive unorientable unit clauses: 0
% 0.47/0.64  #    Negative unit clauses             : 205
% 0.47/0.64  #    Non-unit-clauses                  : 1099
% 0.47/0.64  # Current number of unprocessed clauses: 7735
% 0.47/0.64  # ...number of literals in the above   : 30089
% 0.47/0.64  # Current number of archived formulas  : 0
% 0.47/0.64  # Current number of archived clauses   : 22
% 0.47/0.64  # Clause-clause subsumption calls (NU) : 131853
% 0.47/0.64  # Rec. Clause-clause subsumption calls : 113297
% 0.47/0.64  # Non-unit clause-clause subsumptions  : 63
% 0.47/0.64  # Unit Clause-clause subsumption calls : 8625
% 0.47/0.64  # Rewrite failures with RHS unbound    : 0
% 0.47/0.64  # BW rewrite match attempts            : 4374
% 0.47/0.64  # BW rewrite match successes           : 4
% 0.47/0.64  # Condensation attempts                : 1476
% 0.47/0.64  # Condensation successes               : 0
% 0.47/0.64  # Termbank termtop insertions          : 557333
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.286 s
% 0.47/0.64  # System time              : 0.010 s
% 0.47/0.64  # Total time               : 0.296 s
% 0.47/0.64  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
