%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:33 EST 2020

% Result     : CounterSatisfiable 0.74s
% Output     : Saturation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  231 (38514 expanded)
%              Number of clauses        :  212 (15540 expanded)
%              Number of leaves         :    9 (11482 expanded)
%              Depth                    :   17
%              Number of atoms          : 2347 (164989 expanded)
%              Number of equality atoms :   68 (5474 expanded)
%              Maximal formula depth    :   16 (  11 average)
%              Maximal clause size      :   15 (  11 average)
%              Maximal term depth       :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(t62_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(c_0_9,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v2_funct_1(X12)
      | k2_funct_1(k2_funct_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_10,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v2_funct_1(X11)
      | v2_funct_1(k2_funct_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).

fof(c_0_11,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_12,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_15,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_16,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_17,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))) = k2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_18,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))) = k2_funct_1(k2_funct_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_19,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_20,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_21,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_21]),
    [final]).

cnf(c_0_23,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21]),
    [final]).

fof(c_0_24,plain,(
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

cnf(c_0_25,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]),
    [final]).

cnf(c_0_26,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

cnf(c_0_27,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21]),
    [final]).

cnf(c_0_29,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21]),
    [final]).

cnf(c_0_30,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21]),
    [final]).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_13]),c_0_22]),c_0_23]),
    [final]).

cnf(c_0_32,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_13]),c_0_22]),c_0_23]),
    [final]).

cnf(c_0_33,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21]),
    [final]).

cnf(c_0_34,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21]),
    [final]).

cnf(c_0_36,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_37,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21]),
    [final]).

cnf(c_0_38,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_39,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]),
    [final]).

cnf(c_0_40,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

cnf(c_0_41,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_42,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_43,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_44,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_45,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_46,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

fof(c_0_47,negated_conjecture,(
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

cnf(c_0_48,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_49,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_50,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_51,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_52,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_53,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_54,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_55,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_56,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_57,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21]),
    [final]).

cnf(c_0_58,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]),
    [final]).

cnf(c_0_59,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

cnf(c_0_60,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]),
    [final]).

cnf(c_0_61,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

fof(c_0_62,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k2_relset_1(X13,X14,X15) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_63,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_47])])])])).

fof(c_0_64,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | v1_relat_1(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_65,plain,(
    ! [X6,X7] : v1_relat_1(k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_66,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21]),
    [final]).

cnf(c_0_68,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_69,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_70,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21]),
    [final]).

cnf(c_0_71,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21]),
    [final]).

cnf(c_0_72,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_73,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_74,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_75,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21]),
    [final]).

cnf(c_0_76,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21]),
    [final]).

cnf(c_0_77,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_78,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_79,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21]),
    [final]).

cnf(c_0_80,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_81,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_82,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21]),
    [final]).

cnf(c_0_83,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_84,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_21]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_85,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21]),
    [final]).

cnf(c_0_86,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_87,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21]),
    [final]).

cnf(c_0_88,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_21]),
    [final]).

cnf(c_0_89,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21]),
    [final]).

cnf(c_0_90,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21]),
    [final]).

cnf(c_0_91,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21]),
    [final]).

cnf(c_0_92,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_93,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21]),
    [final]).

cnf(c_0_94,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21]),
    [final]).

cnf(c_0_95,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_21]),
    [final]).

cnf(c_0_96,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_97,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_21]),
    [final]).

cnf(c_0_98,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_21]),
    [final]).

cnf(c_0_99,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21]),
    [final]).

cnf(c_0_100,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_101,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_102,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_21]),
    [final]).

cnf(c_0_103,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_104,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_21]),
    [final]).

cnf(c_0_105,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_106,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_21]),
    [final]).

cnf(c_0_107,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21]),
    [final]).

cnf(c_0_108,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21]),
    [final]).

cnf(c_0_109,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_21]),
    [final]).

cnf(c_0_110,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

fof(c_0_111,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v2_funct_1(X8)
      | k2_funct_1(X8) = k4_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_112,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_114,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64]),
    [final]).

cnf(c_0_115,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_116,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_21]),
    [final]).

cnf(c_0_117,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_21]),
    [final]).

cnf(c_0_118,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_21]),
    [final]).

cnf(c_0_119,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_21]),
    [final]).

cnf(c_0_120,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_21]),
    [final]).

cnf(c_0_121,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_21]),
    [final]).

cnf(c_0_122,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_21]),
    [final]).

cnf(c_0_123,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_21]),
    [final]).

cnf(c_0_124,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_21]),
    [final]).

cnf(c_0_125,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21]),
    [final]).

cnf(c_0_126,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_21]),
    [final]).

cnf(c_0_127,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_21]),
    [final]).

cnf(c_0_128,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_129,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_21]),
    [final]).

cnf(c_0_130,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_21]),
    [final]).

cnf(c_0_131,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21]),
    [final]).

cnf(c_0_132,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_21]),
    [final]).

cnf(c_0_133,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21]),
    [final]).

cnf(c_0_134,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21]),
    [final]).

cnf(c_0_135,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21]),
    [final]).

cnf(c_0_136,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_137,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_138,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21]),
    [final]).

cnf(c_0_139,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_21]),
    [final]).

cnf(c_0_140,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21]),
    [final]).

cnf(c_0_141,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21]),
    [final]).

cnf(c_0_142,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_143,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21]),
    [final]).

cnf(c_0_144,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21]),
    [final]).

cnf(c_0_145,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_146,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_21]),
    [final]).

cnf(c_0_147,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_21]),
    [final]).

cnf(c_0_148,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21]),
    [final]).

cnf(c_0_149,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21]),
    [final]).

cnf(c_0_150,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_21]),
    [final]).

cnf(c_0_151,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21]),
    [final]).

cnf(c_0_152,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21]),
    [final]).

cnf(c_0_153,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21]),
    [final]).

cnf(c_0_154,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_21]),
    [final]).

cnf(c_0_155,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_21]),
    [final]).

cnf(c_0_156,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21]),
    [final]).

cnf(c_0_157,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_21]),
    [final]).

cnf(c_0_158,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_21]),
    [final]).

cnf(c_0_159,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21]),
    [final]).

cnf(c_0_160,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_21]),
    [final]).

cnf(c_0_161,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21]),
    [final]).

cnf(c_0_162,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_21]),
    [final]).

cnf(c_0_163,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_21]),
    [final]).

cnf(c_0_164,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21]),
    [final]).

cnf(c_0_165,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21]),
    [final]).

cnf(c_0_166,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_167,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_21]),
    [final]).

cnf(c_0_168,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21]),
    [final]).

cnf(c_0_169,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21]),
    [final]).

cnf(c_0_170,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21]),
    [final]).

cnf(c_0_171,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_21]),
    [final]).

cnf(c_0_172,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_173,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_21]),
    [final]).

cnf(c_0_174,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_21]),
    [final]).

cnf(c_0_175,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21]),
    [final]).

cnf(c_0_176,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_21]),
    [final]).

cnf(c_0_177,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_21]),
    [final]).

cnf(c_0_178,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_21]),
    [final]).

cnf(c_0_179,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_21]),
    [final]).

cnf(c_0_180,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_21]),
    [final]).

cnf(c_0_181,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_21]),
    [final]).

cnf(c_0_182,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21]),
    [final]).

cnf(c_0_183,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_21]),
    [final]).

cnf(c_0_184,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_185,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21]),
    [final]).

cnf(c_0_186,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21]),
    [final]).

cnf(c_0_187,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_21]),
    [final]).

cnf(c_0_188,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_21]),
    [final]).

cnf(c_0_189,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_21]),
    [final]).

cnf(c_0_190,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_21]),
    [final]).

cnf(c_0_191,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_192,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21]),
    [final]).

cnf(c_0_193,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21]),
    [final]).

cnf(c_0_194,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_21]),
    [final]).

cnf(c_0_195,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_196,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_21]),
    [final]).

cnf(c_0_197,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21]),
    [final]).

cnf(c_0_198,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_21]),
    [final]).

cnf(c_0_199,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_21]),
    [final]).

cnf(c_0_200,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_201,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21]),
    [final]).

cnf(c_0_202,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_21]),
    [final]).

cnf(c_0_203,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_21]),
    [final]).

cnf(c_0_204,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21]),
    [final]).

cnf(c_0_205,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_21]),
    [final]).

cnf(c_0_206,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21]),
    [final]).

cnf(c_0_207,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_21]),
    [final]).

cnf(c_0_208,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_209,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_210,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_21]),
    [final]).

cnf(c_0_211,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_212,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_21]),
    [final]).

cnf(c_0_213,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_214,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21]),
    [final]).

cnf(c_0_215,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_216,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_13]),c_0_14]),c_0_15]),
    [final]).

cnf(c_0_217,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]),
    [final]).

cnf(c_0_218,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

cnf(c_0_219,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(X1))) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_27]),c_0_14]),c_0_15]),c_0_13]),
    [final]).

cnf(c_0_220,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_221,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111]),
    [final]).

cnf(c_0_222,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_223,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_224,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113]),
    [final]).

cnf(c_0_225,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_113]),c_0_115])]),
    [final]).

cnf(c_0_226,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_227,negated_conjecture,
    ( v23_waybel_0(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_228,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_229,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_230,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.74/0.92  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.74/0.92  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.74/0.92  #
% 0.74/0.92  # Preprocessing time       : 0.028 s
% 0.74/0.92  # Presaturation interreduction done
% 0.74/0.92  
% 0.74/0.92  # No proof found!
% 0.74/0.92  # SZS status CounterSatisfiable
% 0.74/0.92  # SZS output start Saturation
% 0.74/0.92  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 0.74/0.92  fof(t62_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 0.74/0.92  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.74/0.92  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.74/0.92  fof(t67_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_waybel_0)).
% 0.74/0.92  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.74/0.92  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.74/0.92  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.74/0.92  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.74/0.92  fof(c_0_9, plain, ![X12]:(~v1_relat_1(X12)|~v1_funct_1(X12)|(~v2_funct_1(X12)|k2_funct_1(k2_funct_1(X12))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.74/0.92  fof(c_0_10, plain, ![X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v2_funct_1(X11)|v2_funct_1(k2_funct_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).
% 0.74/0.92  fof(c_0_11, plain, ![X9]:((v1_relat_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.74/0.92  cnf(c_0_12, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.74/0.92  cnf(c_0_13, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.74/0.92  cnf(c_0_14, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.74/0.92  cnf(c_0_15, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.74/0.92  cnf(c_0_16, plain, (k2_funct_1(k2_funct_1(k2_funct_1(X1)))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_17, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))=k2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_18, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))=k2_funct_1(k2_funct_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_19, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_20, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_21, plain, (k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))=k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_22, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_23, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_21]), ['final']).
% 0.74/0.92  fof(c_0_24, plain, ![X10]:((k2_relat_1(X10)=k1_relat_1(k2_funct_1(X10))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(k1_relat_1(X10)=k2_relat_1(k2_funct_1(X10))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.74/0.92  cnf(c_0_25, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_26, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_27, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.74/0.92  cnf(c_0_28, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_29, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_30, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_31, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_13]), c_0_22]), c_0_23]), ['final']).
% 0.74/0.92  cnf(c_0_32, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_13]), c_0_22]), c_0_23]), ['final']).
% 0.74/0.92  cnf(c_0_33, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_34, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_35, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_36, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_37, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_38, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_39, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_40, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_41, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_42, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_43, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_44, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_45, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_46, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  fof(c_0_47, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t67_waybel_0])).
% 0.74/0.92  cnf(c_0_48, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_49, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_50, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_51, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_52, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_53, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_54, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_55, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_56, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_57, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_58, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_59, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_60, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_61, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.74/0.92  fof(c_0_62, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k2_relset_1(X13,X14,X15)=k2_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.74/0.92  fof(c_0_63, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((~v2_struct_0(esk2_0)&l1_orders_2(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v23_waybel_0(esk3_0,esk1_0,esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_47])])])])).
% 0.74/0.92  fof(c_0_64, plain, ![X4, X5]:(~v1_relat_1(X4)|(~m1_subset_1(X5,k1_zfmisc_1(X4))|v1_relat_1(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.74/0.92  fof(c_0_65, plain, ![X6, X7]:v1_relat_1(k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.74/0.92  cnf(c_0_66, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_67, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_68, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_69, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_70, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_71, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_72, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_73, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_74, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_75, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_76, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_77, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_78, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_79, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_80, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_81, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_82, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_83, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_84, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_21]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_85, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_86, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_87, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_88, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_89, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_90, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_91, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_92, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_93, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_94, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_95, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_96, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_97, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_57, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_98, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_99, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_100, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_101, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_102, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_103, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_104, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_59, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_105, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_106, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_107, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_108, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_109, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_110, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.74/0.92  fof(c_0_111, plain, ![X8]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(~v2_funct_1(X8)|k2_funct_1(X8)=k4_relat_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.74/0.92  cnf(c_0_112, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62]), ['final']).
% 0.74/0.92  cnf(c_0_113, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_114, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64]), ['final']).
% 0.74/0.92  cnf(c_0_115, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 0.74/0.92  cnf(c_0_116, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_117, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_118, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_119, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_69, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_120, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_121, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_122, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_123, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_124, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_125, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_126, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_127, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_128, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_129, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_130, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_78, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_131, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_132, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_79, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_133, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_134, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_135, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_136, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_137, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_138, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_139, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_80, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_140, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_141, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_142, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_143, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_144, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_145, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_146, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_81, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_147, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_82, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_148, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_149, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_150, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_83, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_151, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_152, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_153, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_154, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_155, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_156, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_157, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_86, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_158, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_159, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_160, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_88, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_161, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_162, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_163, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_164, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_165, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_166, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_167, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_168, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_169, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_170, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_171, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_172, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_173, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_90, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_174, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_175, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_176, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_177, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_92, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_178, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_93, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_179, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_94, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_180, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_95, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_181, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_182, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_183, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_96, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_184, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_185, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_186, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_187, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_97, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_188, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_98, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_189, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_99, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_190, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_100, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_191, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_192, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_193, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_194, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_195, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_196, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_101, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_197, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_198, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_199, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_200, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_201, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_202, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_103, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_203, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_104, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_204, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_205, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_105, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_206, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_207, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_208, plain, (k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))=k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_209, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_210, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_107, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_211, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_212, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_108, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_213, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_214, plain, (v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_215, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_216, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_13]), c_0_14]), c_0_15]), ['final']).
% 0.74/0.92  cnf(c_0_217, plain, (v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_218, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))))))|~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1))))))))))|~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X1)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.74/0.92  cnf(c_0_219, plain, (k2_relat_1(k2_funct_1(k2_funct_1(X1)))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_27]), c_0_14]), c_0_15]), c_0_13]), ['final']).
% 0.74/0.92  cnf(c_0_220, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_221, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_111]), ['final']).
% 0.74/0.92  cnf(c_0_222, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_223, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_224, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_112, c_0_113]), ['final']).
% 0.74/0.92  cnf(c_0_225, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_113]), c_0_115])]), ['final']).
% 0.74/0.92  cnf(c_0_226, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_227, negated_conjecture, (v23_waybel_0(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_228, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_229, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  cnf(c_0_230, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.74/0.92  # SZS output end Saturation
% 0.74/0.92  # Proof object total steps             : 231
% 0.74/0.92  # Proof object clause steps            : 212
% 0.74/0.92  # Proof object formula steps           : 19
% 0.74/0.92  # Proof object conjectures             : 14
% 0.74/0.92  # Proof object clause conjectures      : 11
% 0.74/0.92  # Proof object formula conjectures     : 3
% 0.74/0.92  # Proof object initial clauses used    : 19
% 0.74/0.92  # Proof object initial formulas used   : 9
% 0.74/0.92  # Proof object generating inferences   : 193
% 0.74/0.92  # Proof object simplifying inferences  : 71
% 0.74/0.92  # Parsed axioms                        : 9
% 0.74/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.74/0.92  # Initial clauses                      : 19
% 0.74/0.92  # Removed in clause preprocessing      : 0
% 0.74/0.92  # Initial clauses in saturation        : 19
% 0.74/0.92  # Processed clauses                    : 2371
% 0.74/0.92  # ...of these trivial                  : 0
% 0.74/0.92  # ...subsumed                          : 2138
% 0.74/0.92  # ...remaining for further processing  : 233
% 0.74/0.92  # Other redundant clauses eliminated   : 0
% 0.74/0.92  # Clauses deleted for lack of memory   : 0
% 0.74/0.92  # Backward-subsumed                    : 2
% 0.74/0.92  # Backward-rewritten                   : 0
% 0.74/0.92  # Generated clauses                    : 2435
% 0.74/0.92  # ...of the previous two non-trivial   : 2346
% 0.74/0.92  # Contextual simplify-reflections      : 69
% 0.74/0.92  # Paramodulations                      : 2435
% 0.74/0.92  # Factorizations                       : 0
% 0.74/0.92  # Equation resolutions                 : 0
% 0.74/0.92  # Propositional unsat checks           : 0
% 0.74/0.92  #    Propositional check models        : 0
% 0.74/0.92  #    Propositional check unsatisfiable : 0
% 0.74/0.92  #    Propositional clauses             : 0
% 0.74/0.92  #    Propositional clauses after purity: 0
% 0.74/0.92  #    Propositional unsat core size     : 0
% 0.74/0.92  #    Propositional preprocessing time  : 0.000
% 0.74/0.92  #    Propositional encoding time       : 0.000
% 0.74/0.92  #    Propositional solver time         : 0.000
% 0.74/0.92  #    Success case prop preproc time    : 0.000
% 0.74/0.92  #    Success case prop encoding time   : 0.000
% 0.74/0.92  #    Success case prop solver time     : 0.000
% 0.74/0.92  # Current number of processed clauses  : 212
% 0.74/0.92  #    Positive orientable unit clauses  : 9
% 0.74/0.92  #    Positive unorientable unit clauses: 0
% 0.74/0.92  #    Negative unit clauses             : 2
% 0.74/0.92  #    Non-unit-clauses                  : 201
% 0.74/0.92  # Current number of unprocessed clauses: 0
% 0.74/0.92  # ...number of literals in the above   : 0
% 0.74/0.92  # Current number of archived formulas  : 0
% 0.74/0.92  # Current number of archived clauses   : 21
% 0.74/0.92  # Clause-clause subsumption calls (NU) : 191712
% 0.74/0.92  # Rec. Clause-clause subsumption calls : 72391
% 0.74/0.92  # Non-unit clause-clause subsumptions  : 2209
% 0.74/0.92  # Unit Clause-clause subsumption calls : 0
% 0.74/0.92  # Rewrite failures with RHS unbound    : 0
% 0.74/0.92  # BW rewrite match attempts            : 0
% 0.74/0.92  # BW rewrite match successes           : 0
% 0.74/0.92  # Condensation attempts                : 0
% 0.74/0.92  # Condensation successes               : 0
% 0.74/0.92  # Termbank termtop insertions          : 418140
% 0.74/0.92  
% 0.74/0.92  # -------------------------------------------------
% 0.74/0.92  # User time                : 0.559 s
% 0.74/0.92  # System time              : 0.005 s
% 0.74/0.92  # Total time               : 0.565 s
% 0.74/0.92  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
