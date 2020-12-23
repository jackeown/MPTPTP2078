%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1846+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 13.41s
% Output     : CNFRefutation 13.41s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 107 expanded)
%              Number of clauses        :   22 (  38 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 550 expanded)
%              Number of equality atoms :   20 (  84 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v1_subset_1(X3,u1_struct_0(X1))
                <=> v1_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t1_tsep_1)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => ( v1_subset_1(X3,u1_struct_0(X1))
                  <=> v1_tex_2(X2,X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_tex_2])).

fof(c_0_7,plain,(
    ! [X11608,X11609] :
      ( ( ~ v1_subset_1(X11609,X11608)
        | X11609 != X11608
        | ~ m1_subset_1(X11609,k1_zfmisc_1(X11608)) )
      & ( X11609 = X11608
        | v1_subset_1(X11609,X11608)
        | ~ m1_subset_1(X11609,k1_zfmisc_1(X11608)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1327_0)
    & m1_pre_topc(esk1328_0,esk1327_0)
    & m1_subset_1(esk1329_0,k1_zfmisc_1(u1_struct_0(esk1327_0)))
    & esk1329_0 = u1_struct_0(esk1328_0)
    & ( ~ v1_subset_1(esk1329_0,u1_struct_0(esk1327_0))
      | ~ v1_tex_2(esk1328_0,esk1327_0) )
    & ( v1_subset_1(esk1329_0,u1_struct_0(esk1327_0))
      | v1_tex_2(esk1328_0,esk1327_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X11604,X11605,X11606] :
      ( ( ~ v1_tex_2(X11605,X11604)
        | ~ m1_subset_1(X11606,k1_zfmisc_1(u1_struct_0(X11604)))
        | X11606 != u1_struct_0(X11605)
        | v1_subset_1(X11606,u1_struct_0(X11604))
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) )
      & ( m1_subset_1(esk1302_2(X11604,X11605),k1_zfmisc_1(u1_struct_0(X11604)))
        | v1_tex_2(X11605,X11604)
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) )
      & ( esk1302_2(X11604,X11605) = u1_struct_0(X11605)
        | v1_tex_2(X11605,X11604)
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) )
      & ( ~ v1_subset_1(esk1302_2(X11604,X11605),u1_struct_0(X11604))
        | v1_tex_2(X11605,X11604)
        | ~ m1_pre_topc(X11605,X11604)
        | ~ l1_pre_topc(X11604) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk1329_0,k1_zfmisc_1(u1_struct_0(esk1327_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1302_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_pre_topc(esk1328_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( esk1302_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( esk1329_0 = u1_struct_0(esk1328_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X11076,X11077] :
      ( ~ l1_pre_topc(X11076)
      | ~ m1_pre_topc(X11077,X11076)
      | m1_subset_1(u1_struct_0(X11077),k1_zfmisc_1(u1_struct_0(X11076))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_subset_1(esk1329_0,u1_struct_0(esk1327_0))
    | ~ v1_tex_2(esk1328_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( u1_struct_0(esk1327_0) = esk1329_0
    | v1_subset_1(esk1329_0,u1_struct_0(esk1327_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_tex_2(esk1328_0,esk1327_0)
    | ~ v1_subset_1(esk1302_2(esk1327_0,esk1328_0),u1_struct_0(esk1327_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( esk1302_2(esk1327_0,esk1328_0) = esk1329_0
    | v1_tex_2(esk1328_0,esk1327_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( v1_subset_1(esk1329_0,u1_struct_0(esk1327_0))
    | v1_tex_2(esk1328_0,esk1327_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_23,plain,(
    ! [X1956] : ~ v1_subset_1(k2_subset_1(X1956),X1956) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_24,plain,(
    ! [X1539] : k2_subset_1(X1539) = X1539 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_25,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk1327_0) = esk1329_0
    | ~ v1_tex_2(esk1328_0,esk1327_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_tex_2(esk1328_0,esk1327_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_29,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk1327_0) = esk1329_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_33,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_13]),c_0_16]),c_0_32]),c_0_28]),c_0_14])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
