%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1845+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :   16 (  28 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   44 ( 104 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v2_pre_topc(X1) )
           => v2_pre_topc(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tex_2)).

fof(t58_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',t58_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc6_pre_topc)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v2_pre_topc(X1) )
             => v2_pre_topc(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tex_2])).

fof(c_0_4,plain,(
    ! [X6066] :
      ( ~ l1_pre_topc(X6066)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X6066),u1_pre_topc(X6066)))
      | v2_pre_topc(X6066) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).

fof(c_0_5,negated_conjecture,
    ( l1_pre_topc(esk1326_0)
    & l1_pre_topc(esk1327_0)
    & g1_pre_topc(u1_struct_0(esk1326_0),u1_pre_topc(esk1326_0)) = g1_pre_topc(u1_struct_0(esk1327_0),u1_pre_topc(esk1327_0))
    & v2_pre_topc(esk1326_0)
    & ~ v2_pre_topc(esk1327_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X5939] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X5939),u1_pre_topc(X5939)))
        | ~ v2_pre_topc(X5939)
        | ~ l1_pre_topc(X5939) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X5939),u1_pre_topc(X5939)))
        | ~ v2_pre_topc(X5939)
        | ~ l1_pre_topc(X5939) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_7,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1326_0),u1_pre_topc(esk1326_0)) = g1_pre_topc(u1_struct_0(esk1327_0),u1_pre_topc(esk1327_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_pre_topc(esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1326_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1326_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1326_0),u1_pre_topc(esk1326_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
