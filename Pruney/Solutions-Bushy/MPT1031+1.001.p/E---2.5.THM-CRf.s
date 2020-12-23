%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1031+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:36 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 (3890 expanded)
%              Number of clauses        :   63 (1436 expanded)
%              Number of leaves         :   14 ( 963 expanded)
%              Depth                    :   16
%              Number of atoms          :  425 (35144 expanded)
%              Number of equality atoms :   46 (6447 expanded)
%              Maximal formula depth    :   36 (   5 average)
%              Maximal clause size      :  140 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t136_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ? [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                  & k1_funct_1(X4,X5) != k1_funct_1(X3,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(s5_funct_2__e3_154_1_2__funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ( r2_hidden(X4,X1)
           => ( ( r2_hidden(X4,k1_relset_1(X1,X2,X3))
               => r2_hidden(k1_funct_1(X3,X4),X2) )
              & ( ~ r2_hidden(X4,k1_relset_1(X1,X2,X3))
               => r2_hidden(o_1_1_funct_2(X2),X2) ) ) )
       => ? [X4] :
            ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & ! [X5] :
                ( r2_hidden(X5,X1)
               => ( ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                   => k1_funct_1(X4,X5) = k1_funct_1(X3,X5) )
                  & ( ~ r2_hidden(X5,k1_relset_1(X1,X2,X3))
                   => k1_funct_1(X4,X5) = o_1_1_funct_2(X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s5_funct_2__e3_154_1_2__funct_2)).

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

fof(t27_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,k1_relat_1(X3))
       => r2_hidden(k1_funct_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_partfun1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_o_1_1_funct_2,axiom,(
    ! [X1] : m1_subset_1(o_1_1_funct_2(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
            & ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ? [X5] :
                    ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                    & k1_funct_1(X4,X5) != k1_funct_1(X3,X5) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t136_funct_2])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,negated_conjecture,(
    ! [X43] :
      ( v1_funct_1(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( esk4_0 != k1_xboole_0
        | esk3_0 = k1_xboole_0 )
      & ( r2_hidden(esk6_1(X43),k1_relset_1(esk3_0,esk4_0,esk5_0))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,esk3_0,esk4_0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) )
      & ( k1_funct_1(X43,esk6_1(X43)) != k1_funct_1(esk5_0,esk6_1(X43))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,esk3_0,esk4_0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X30] :
      ( ( v1_funct_1(esk2_3(X25,X26,X27))
        | r2_hidden(esk1_3(X25,X26,X27),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_2(esk2_3(X25,X26,X27),X25,X26)
        | r2_hidden(esk1_3(X25,X26,X27),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | r2_hidden(esk1_3(X25,X26,X27),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = k1_funct_1(X27,X30)
        | ~ r2_hidden(X30,X25)
        | r2_hidden(esk1_3(X25,X26,X27),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = o_1_1_funct_2(X26)
        | ~ r2_hidden(X30,X25)
        | r2_hidden(esk1_3(X25,X26,X27),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_1(esk2_3(X25,X26,X27))
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_2(esk2_3(X25,X26,X27),X25,X26)
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = k1_funct_1(X27,X30)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = o_1_1_funct_2(X26)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_1(esk2_3(X25,X26,X27))
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_2(esk2_3(X25,X26,X27),X25,X26)
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = k1_funct_1(X27,X30)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = o_1_1_funct_2(X26)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_1(esk2_3(X25,X26,X27))
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_2(esk2_3(X25,X26,X27),X25,X26)
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = k1_funct_1(X27,X30)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = o_1_1_funct_2(X26)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(esk1_3(X25,X26,X27),k1_relset_1(X25,X26,X27))
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_1(esk2_3(X25,X26,X27))
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_2(esk2_3(X25,X26,X27),X25,X26)
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = k1_funct_1(X27,X30)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(X30,k1_relset_1(X25,X26,X27))
        | k1_funct_1(esk2_3(X25,X26,X27),X30) = o_1_1_funct_2(X26)
        | ~ r2_hidden(X30,X25)
        | ~ r2_hidden(o_1_1_funct_2(X26),X26)
        | ~ r2_hidden(k1_funct_1(X27,esk1_3(X25,X26,X27)),X26)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s5_funct_2__e3_154_1_2__funct_2])])])])])])).

cnf(c_0_18,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk2_3(X1,X2,X3))
    | ~ r2_hidden(esk1_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(k1_funct_1(X3,esk1_3(X1,X2,X3)),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v5_relat_1(X33,X31)
      | ~ v1_funct_1(X33)
      | ~ r2_hidden(X32,k1_relat_1(X33))
      | r2_hidden(k1_funct_1(X33,X32),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_partfun1])])).

cnf(c_0_26,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_funct_2(esk2_3(X1,X2,X3),X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(k1_funct_1(X3,esk1_3(X1,X2,X3)),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k1_funct_1(esk2_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(esk1_3(X2,X3,X4),k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(k1_funct_1(X4,esk1_3(X2,X3,X4)),X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_1(X1),k1_relset_1(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk1_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(k1_funct_1(X3,esk1_3(X1,X2,X3)),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_37,plain,
    ( k1_funct_1(esk2_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | r2_hidden(esk1_3(X2,X3,X4),k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(o_1_1_funct_2(X3),X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_38,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X34,X35)
      | v1_xboole_0(X35)
      | r2_hidden(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_39,plain,(
    ! [X21] : m1_subset_1(o_1_1_funct_2(X21),X21) ),
    inference(variable_rename,[status(thm)],[dt_o_1_1_funct_2])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0),X1) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_1(X1),k1_relat_1(esk5_0))
    | ~ v1_funct_2(X1,esk3_0,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34]),c_0_35]),c_0_24])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(X1,esk6_1(X1)) != k1_funct_1(esk5_0,esk6_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0),X1) = k1_funct_1(esk5_0,X1)
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_24])]),c_0_23]),c_0_23])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( m1_subset_1(o_1_1_funct_2(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0),X1) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_34]),c_0_35]),c_0_24])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])).

fof(c_0_51,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | m1_subset_1(k1_relset_1(X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(o_1_1_funct_2(X2),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( v1_funct_1(esk2_3(X1,X2,X3))
    | r2_hidden(esk1_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(o_1_1_funct_2(X2),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,plain,
    ( v1_funct_2(esk2_3(X1,X2,X3),X1,X2)
    | r2_hidden(esk1_3(X1,X2,X3),k1_relset_1(X1,X2,X3))
    | ~ r2_hidden(o_1_1_funct_2(X2),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0),esk6_1(esk2_3(esk3_0,esk4_0,esk5_0))) != k1_funct_1(esk5_0,esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0),X1) = k1_funct_1(esk5_0,X1)
    | v1_xboole_0(esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),k1_relat_1(esk5_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_34]),c_0_35]),c_0_24])])).

fof(c_0_58,plain,(
    ! [X6,X7,X8] :
      ( ( v1_funct_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_partfun1(X8,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( v1_funct_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_partfun1(X8,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_59,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_60,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_24]),c_0_19])]),c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0)
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_23]),c_0_24]),c_0_19])]),c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | ~ r2_hidden(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

fof(c_0_65,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_partfun1(X11,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_66,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_24])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_23]),c_0_19])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | k1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0),esk6_1(esk2_3(esk3_0,esk4_0,esk5_0))) != k1_funct_1(esk5_0,esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),k1_relat_1(esk5_0))
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_61]),c_0_62]),c_0_63]),c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk5_0),k1_relat_1(esk5_0))
    | ~ r2_hidden(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_34]),c_0_35]),c_0_24])])).

cnf(c_0_73,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_partfun1(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_19]),c_0_24])]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_76,plain,(
    ! [X39] :
      ( ~ v1_xboole_0(X39)
      | X39 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r2_hidden(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),esk3_0)
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_56]),c_0_71]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_19]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk6_1(esk2_3(esk3_0,esk4_0,esk5_0)),esk3_0)
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_71])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r2_hidden(o_1_1_funct_2(esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_47]),c_0_78]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_84,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_47]),c_0_48])])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | esk4_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_81]),c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_88]),c_0_89])]),
    [proof]).

%------------------------------------------------------------------------------
