%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:33 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   90 (3257 expanded)
%              Number of clauses        :   71 (1251 expanded)
%              Number of leaves         :    9 ( 998 expanded)
%              Depth                    :   12
%              Number of atoms          :  524 (18193 expanded)
%              Number of equality atoms :  142 (2455 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal clause size      :   12 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(t63_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_waybel_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_9,plain,(
    ! [X11] :
      ( ( k5_relat_1(X11,k2_funct_1(X11)) = k6_relat_1(k1_relat_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( k5_relat_1(k2_funct_1(X11),X11) = k6_relat_1(k2_relat_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_10,plain,(
    ! [X10] :
      ( ( k2_relat_1(X10) = k1_relat_1(k2_funct_1(X10))
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k1_relat_1(X10) = k2_relat_1(k2_funct_1(X10))
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_11,plain,(
    ! [X8] :
      ( ( v1_relat_1(k2_funct_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( v1_funct_1(k2_funct_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_12,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) )
      & ( v2_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_13,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_16,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v2_funct_1(X12)
      | k2_relat_1(X12) != k1_relat_1(X13)
      | k5_relat_1(X12,X13) != k6_relat_1(k1_relat_1(X12))
      | X13 = k2_funct_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).

cnf(c_0_19,plain,
    ( k5_relat_1(k2_funct_1(X1),k2_funct_1(k2_funct_1(X1))) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_20,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_21,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_22,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_23,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(X1))) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_19]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(X2,X1) != k5_relat_1(X2,k2_funct_1(X2))
    | k1_relat_1(X1) != k2_relat_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13]),
    [final]).

cnf(c_0_25,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15]),c_0_16]),c_0_17]),c_0_22]),c_0_23]),
    [final]).

cnf(c_0_26,plain,
    ( X1 = X2
    | k5_relat_1(k2_funct_1(X2),X1) != k5_relat_1(k2_funct_1(X2),X2)
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_27,plain,
    ( X1 = X2
    | k5_relat_1(k2_funct_1(X2),X1) != k6_relat_1(k2_relat_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21]),
    [final]).

cnf(c_0_28,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_25]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_29,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1) != k6_relat_1(k1_relat_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_30,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_31,plain,
    ( k5_relat_1(k2_funct_1(X1),k2_funct_1(k2_funct_1(X1))) = k5_relat_1(k2_funct_1(X1),X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_28]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_32,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1) != k5_relat_1(X2,k2_funct_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_13]),
    [final]).

cnf(c_0_33,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k5_relat_1(k2_funct_1(X2),X2)
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_34,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_35,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(X2),X1) != k6_relat_1(k2_relat_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

fof(c_0_36,negated_conjecture,(
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

cnf(c_0_37,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k5_relat_1(X1,k2_funct_1(X1))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_38,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k6_relat_1(k1_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28]),
    [final]).

cnf(c_0_39,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_40,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k6_relat_1(k2_relat_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1) != k6_relat_1(k2_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30]),
    [final]).

cnf(c_0_42,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(X2)))
    | k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1) != k6_relat_1(k1_relat_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

fof(c_0_43,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k2_relset_1(X14,X15,X16) = k2_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v23_waybel_0(esk3_0,esk1_0,esk2_0)
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
      | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

fof(c_0_45,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | v1_relat_1(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_46,plain,(
    ! [X6,X7] : v1_relat_1(k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_47,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))) != k5_relat_1(k2_funct_1(X1),X1)
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_48,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))) != k6_relat_1(k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_49,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))) != k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_50,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))) != k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_51,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_52,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k6_relat_1(k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_53,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k5_relat_1(k2_funct_1(X2),X2)
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_54,plain,
    ( X1 = X2
    | k5_relat_1(k2_funct_1(X2),X1) != k6_relat_1(k1_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28]),
    [final]).

cnf(c_0_55,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(X2)))
    | k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1) != k5_relat_1(X2,k2_funct_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_56,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(X2),X1) != k5_relat_1(k2_funct_1(X2),X2)
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21]),
    [final]).

cnf(c_0_57,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_59,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_60,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46]),
    [final]).

cnf(c_0_61,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k5_relat_1(k2_funct_1(X1),X1)
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_22]),
    [final]).

cnf(c_0_62,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k6_relat_1(k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22]),
    [final]).

cnf(c_0_63,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(X1)))) != k5_relat_1(X1,k2_funct_1(X1))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_13]),c_0_15]),c_0_16]),c_0_14]),
    [final]).

cnf(c_0_64,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_22]),
    [final]).

cnf(c_0_65,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) != k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22]),
    [final]).

cnf(c_0_66,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(X1)))) != k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_22]),
    [final]).

cnf(c_0_67,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(X1)))) != k6_relat_1(k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_22]),
    [final]).

cnf(c_0_68,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k6_relat_1(k1_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28]),
    [final]).

cnf(c_0_69,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_34]),
    [final]).

cnf(c_0_70,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1) != k6_relat_1(k2_relat_1(X2))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_71,plain,
    ( X1 = X2
    | k5_relat_1(k2_funct_1(X2),X1) != k5_relat_1(k2_funct_1(X2),k2_funct_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_13]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_72,plain,
    ( X1 = k2_funct_1(k2_funct_1(k2_funct_1(X2)))
    | k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1) != k6_relat_1(k2_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(k2_funct_1(X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_30]),
    [final]).

cnf(c_0_73,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(X2),X1) != k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_34]),
    [final]).

cnf(c_0_74,plain,
    ( X1 = k2_funct_1(k2_funct_1(X2))
    | k5_relat_1(k2_funct_1(X2),X1) != k6_relat_1(k1_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_28]),
    [final]).

cnf(c_0_75,plain,
    ( X1 = X2
    | k5_relat_1(k2_funct_1(X2),X1) != k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))
    | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_34]),
    [final]).

cnf(c_0_76,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1)))) = k6_relat_1(k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34]),
    [final]).

cnf(c_0_77,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1)))) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_30]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_78,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(k2_funct_1(X2)))
    | k1_relat_1(X1) != k2_relat_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30]),
    [final]).

cnf(c_0_79,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(X1))) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25]),c_0_15]),c_0_16]),c_0_17]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_60])]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( v23_waybel_0(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:24 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  # Version: 2.5pre002
% 0.18/0.33  # No SInE strategy applied
% 0.18/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.027 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # No proof found!
% 0.18/0.39  # SZS status CounterSatisfiable
% 0.18/0.39  # SZS output start Saturation
% 0.18/0.39  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.18/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.18/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.18/0.39  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.18/0.39  fof(t63_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 0.18/0.39  fof(t67_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_waybel_0)).
% 0.18/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.18/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.39  fof(c_0_9, plain, ![X11]:((k5_relat_1(X11,k2_funct_1(X11))=k6_relat_1(k1_relat_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(k5_relat_1(k2_funct_1(X11),X11)=k6_relat_1(k2_relat_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.18/0.39  fof(c_0_10, plain, ![X10]:((k2_relat_1(X10)=k1_relat_1(k2_funct_1(X10))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(k1_relat_1(X10)=k2_relat_1(k2_funct_1(X10))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.18/0.39  fof(c_0_11, plain, ![X8]:((v1_relat_1(k2_funct_1(X8))|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(v1_funct_1(k2_funct_1(X8))|(~v1_relat_1(X8)|~v1_funct_1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.18/0.39  fof(c_0_12, plain, ![X9]:(((v1_relat_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9)))&(v1_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9))))&(v2_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.18/0.39  cnf(c_0_13, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.39  cnf(c_0_14, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.39  cnf(c_0_15, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.39  cnf(c_0_16, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.39  cnf(c_0_17, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.18/0.39  fof(c_0_18, plain, ![X12, X13]:(~v1_relat_1(X12)|~v1_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)|(~v2_funct_1(X12)|k2_relat_1(X12)!=k1_relat_1(X13)|k5_relat_1(X12,X13)!=k6_relat_1(k1_relat_1(X12))|X13=k2_funct_1(X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).
% 0.18/0.39  cnf(c_0_19, plain, (k5_relat_1(k2_funct_1(X1),k2_funct_1(k2_funct_1(X1)))=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_20, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.18/0.39  cnf(c_0_21, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.39  cnf(c_0_22, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.39  cnf(c_0_23, plain, (k6_relat_1(k1_relat_1(k2_funct_1(X1)))=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_19]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_24, plain, (X1=k2_funct_1(X2)|k5_relat_1(X2,X1)!=k5_relat_1(X2,k2_funct_1(X2))|k1_relat_1(X1)!=k2_relat_1(X2)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_20, c_0_13]), ['final']).
% 0.18/0.39  cnf(c_0_25, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15]), c_0_16]), c_0_17]), c_0_22]), c_0_23]), ['final']).
% 0.18/0.39  cnf(c_0_26, plain, (X1=X2|k5_relat_1(k2_funct_1(X2),X1)!=k5_relat_1(k2_funct_1(X2),X2)|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_27, plain, (X1=X2|k5_relat_1(k2_funct_1(X2),X1)!=k6_relat_1(k2_relat_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_26, c_0_21]), ['final']).
% 0.18/0.39  cnf(c_0_28, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_25]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_29, plain, (X1=k2_funct_1(X2)|k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1)!=k6_relat_1(k1_relat_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(X2)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_30, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_31, plain, (k5_relat_1(k2_funct_1(X1),k2_funct_1(k2_funct_1(X1)))=k5_relat_1(k2_funct_1(X1),X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_28]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_32, plain, (X1=k2_funct_1(X2)|k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1)!=k5_relat_1(X2,k2_funct_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(X2)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_13]), ['final']).
% 0.18/0.39  cnf(c_0_33, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k5_relat_1(k2_funct_1(X2),X2)|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_34, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_35, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(X2),X1)!=k6_relat_1(k2_relat_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  fof(c_0_36, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t67_waybel_0])).
% 0.18/0.39  cnf(c_0_37, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k5_relat_1(X1,k2_funct_1(X1))|~v2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(X1)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_38, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k6_relat_1(k1_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_33, c_0_28]), ['final']).
% 0.18/0.39  cnf(c_0_39, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.18/0.39  cnf(c_0_40, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k6_relat_1(k2_relat_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_14]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_41, plain, (X1=k2_funct_1(X2)|k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1)!=k6_relat_1(k2_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(X2)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_32, c_0_30]), ['final']).
% 0.18/0.39  cnf(c_0_42, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(X2)))|k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1)!=k6_relat_1(k1_relat_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(X2)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  fof(c_0_43, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k2_relset_1(X14,X15,X16)=k2_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.18/0.39  fof(c_0_44, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((~v2_struct_0(esk2_0)&l1_orders_2(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v23_waybel_0(esk3_0,esk1_0,esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).
% 0.18/0.39  fof(c_0_45, plain, ![X4, X5]:(~v1_relat_1(X4)|(~m1_subset_1(X5,k1_zfmisc_1(X4))|v1_relat_1(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.39  fof(c_0_46, plain, ![X6, X7]:v1_relat_1(k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.39  cnf(c_0_47, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))!=k5_relat_1(k2_funct_1(X1),X1)|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_48, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))!=k6_relat_1(k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_49, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))!=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_50, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))!=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_51, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(X1)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_52, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k6_relat_1(k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(X1)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_53, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k5_relat_1(k2_funct_1(X2),X2)|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_54, plain, (X1=X2|k5_relat_1(k2_funct_1(X2),X1)!=k6_relat_1(k1_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_26, c_0_28]), ['final']).
% 0.18/0.39  cnf(c_0_55, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(X2)))|k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1)!=k5_relat_1(X2,k2_funct_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(X2)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_56, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(X2),X1)!=k5_relat_1(k2_funct_1(X2),X2)|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_35, c_0_21]), ['final']).
% 0.18/0.39  cnf(c_0_57, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_59, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.18/0.39  cnf(c_0_60, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46]), ['final']).
% 0.18/0.39  cnf(c_0_61, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k5_relat_1(k2_funct_1(X1),X1)|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_22]), ['final']).
% 0.18/0.39  cnf(c_0_62, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k6_relat_1(k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_22]), ['final']).
% 0.18/0.39  cnf(c_0_63, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))))!=k5_relat_1(X1,k2_funct_1(X1))|~v2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(X1)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_13]), c_0_15]), c_0_16]), c_0_14]), ['final']).
% 0.18/0.39  cnf(c_0_64, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_22]), ['final']).
% 0.18/0.39  cnf(c_0_65, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))!=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_22]), ['final']).
% 0.18/0.39  cnf(c_0_66, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))))!=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_22]), ['final']).
% 0.18/0.39  cnf(c_0_67, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1(X1))))!=k6_relat_1(k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_22]), ['final']).
% 0.18/0.39  cnf(c_0_68, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k6_relat_1(k1_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_53, c_0_28]), ['final']).
% 0.18/0.39  cnf(c_0_69, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_53, c_0_34]), ['final']).
% 0.18/0.39  cnf(c_0_70, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|k5_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))),X1)!=k6_relat_1(k2_relat_1(X2))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X2))))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_14]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_71, plain, (X1=X2|k5_relat_1(k2_funct_1(X2),X1)!=k5_relat_1(k2_funct_1(X2),k2_funct_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_13]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_72, plain, (X1=k2_funct_1(k2_funct_1(k2_funct_1(X2)))|k5_relat_1(k2_funct_1(k2_funct_1(X2)),X1)!=k6_relat_1(k2_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(k2_funct_1(X2)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_55, c_0_30]), ['final']).
% 0.18/0.39  cnf(c_0_73, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(X2),X1)!=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_56, c_0_34]), ['final']).
% 0.18/0.39  cnf(c_0_74, plain, (X1=k2_funct_1(k2_funct_1(X2))|k5_relat_1(k2_funct_1(X2),X1)!=k6_relat_1(k1_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_56, c_0_28]), ['final']).
% 0.18/0.39  cnf(c_0_75, plain, (X1=X2|k5_relat_1(k2_funct_1(X2),X1)!=k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X2))))|k1_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_26, c_0_34]), ['final']).
% 0.18/0.39  cnf(c_0_76, plain, (k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))=k6_relat_1(k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_34]), ['final']).
% 0.18/0.39  cnf(c_0_77, plain, (k6_relat_1(k2_relat_1(k2_funct_1(k2_funct_1(X1))))=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_30]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_78, plain, (X1=k2_funct_1(X2)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(k2_funct_1(X2)))|k1_relat_1(X1)!=k2_relat_1(X2)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_24, c_0_30]), ['final']).
% 0.18/0.39  cnf(c_0_79, plain, (k6_relat_1(k2_relat_1(k2_funct_1(X1)))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_25]), c_0_15]), c_0_16]), c_0_17]), ['final']).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_81, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_83, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['final']).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_60])]), ['final']).
% 0.18/0.39  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_86, negated_conjecture, (v23_waybel_0(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_87, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_88, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  cnf(c_0_89, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.18/0.39  # SZS output end Saturation
% 0.18/0.39  # Proof object total steps             : 90
% 0.18/0.39  # Proof object clause steps            : 71
% 0.18/0.39  # Proof object formula steps           : 19
% 0.18/0.39  # Proof object conjectures             : 14
% 0.18/0.39  # Proof object clause conjectures      : 11
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 20
% 0.18/0.39  # Proof object initial formulas used   : 9
% 0.18/0.39  # Proof object generating inferences   : 51
% 0.18/0.39  # Proof object simplifying inferences  : 85
% 0.18/0.39  # Parsed axioms                        : 9
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 22
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 22
% 0.18/0.39  # Processed clauses                    : 466
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 371
% 0.18/0.39  # ...remaining for further processing  : 95
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 4
% 0.18/0.39  # Backward-rewritten                   : 0
% 0.18/0.39  # Generated clauses                    : 453
% 0.18/0.39  # ...of the previous two non-trivial   : 448
% 0.18/0.39  # Contextual simplify-reflections      : 83
% 0.18/0.39  # Paramodulations                      : 449
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 4
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 71
% 0.18/0.39  #    Positive orientable unit clauses  : 9
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 2
% 0.18/0.39  #    Non-unit-clauses                  : 60
% 0.18/0.39  # Current number of unprocessed clauses: 0
% 0.18/0.39  # ...number of literals in the above   : 0
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 24
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 8868
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 815
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 458
% 0.18/0.39  # Unit Clause-clause subsumption calls : 1
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 0
% 0.18/0.39  # BW rewrite match successes           : 0
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 21947
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.060 s
% 0.18/0.39  # System time              : 0.003 s
% 0.18/0.39  # Total time               : 0.063 s
% 0.18/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
