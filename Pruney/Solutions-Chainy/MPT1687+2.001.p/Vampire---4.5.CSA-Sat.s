%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:19 EST 2020

% Result     : CounterSatisfiable 5.55s
% Output     : Saturation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  345 ( 345 expanded)
%              Number of leaves         :  345 ( 345 expanded)
%              Depth                    :    0
%              Number of atoms          : 2446 (2446 expanded)
%              Number of equality atoms :  904 ( 904 expanded)
%              Maximal formula depth    :   15 (   9 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u3663,axiom,
    ( ~ ! [X1,X0] :
          ( k1_xboole_0 != X0
          | ~ r2_hidden(X1,k1_zfmisc_1(X0))
          | k1_xboole_0 = X1 )
    | ! [X1,X0] :
        ( k1_xboole_0 != X0
        | ~ r2_hidden(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1 ) )).

tff(u3662,axiom,
    ( ~ ! [X0,X2] :
          ( k1_xboole_0 != k3_tarski(X0)
          | ~ r2_hidden(X2,X0)
          | k1_xboole_0 = X2 )
    | ! [X0,X2] :
        ( k1_xboole_0 != k3_tarski(X0)
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X2 ) )).

tff(u3661,negated_conjecture,
    ( ~ ( k1_xboole_0 != k2_relat_1(sK2) )
    | k1_xboole_0 != k2_relat_1(sK2) )).

tff(u3660,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | k1_xboole_0 != u1_struct_0(sK1) )).

tff(u3659,axiom,
    ( ~ ! [X0] :
          ( k1_xboole_0 != sK3(X0)
          | k1_xboole_0 = k3_tarski(X0) )
    | ! [X0] :
        ( k1_xboole_0 != sK3(X0)
        | k1_xboole_0 = k3_tarski(X0) ) )).

tff(u3658,negated_conjecture,
    ( ~ ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) )
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) )).

tff(u3657,negated_conjecture,
    ( ~ ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2) )
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2) )).

tff(u3656,negated_conjecture,
    ( ~ ( sK2 != k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) )
    | sK2 != k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) )).

tff(u3655,negated_conjecture,
    ( ~ ( sK2 != k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)) )
    | sK2 != k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)) )).

tff(u3654,axiom,
    ( ~ ! [X0] : k1_xboole_0 = k1_subset_1(X0)
    | ! [X0] : k1_xboole_0 = k1_subset_1(X0) )).

tff(u3653,axiom,
    ( ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 )).

tff(u3652,axiom,
    ( ~ ! [X1,X0] : k2_relat_1(k2_zfmisc_1(X0,X1)) = k2_relset_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
    | ! [X1,X0] : k2_relat_1(k2_zfmisc_1(X0,X1)) = k2_relset_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) )).

tff(u3651,negated_conjecture,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) )).

tff(u3650,axiom,
    ( ~ ! [X1,X0] :
          ( k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ! [X1,X0] :
        ( k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )).

tff(u3649,axiom,
    ( ~ ! [X3,X4] :
          ( k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X3,k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)) )
    | ! [X3,X4] :
        ( k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X3,k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)) ) )).

tff(u3648,axiom,
    ( ~ ! [X16,X15,X17,X14] :
          ( k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X14,k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))
          | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) )
    | ! [X16,X15,X17,X14] :
        ( k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X14,k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))
        | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) ) )).

tff(u3647,axiom,
    ( ~ ! [X1,X0,X2] :
          ( k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) )
    | ! [X1,X0,X2] :
        ( k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) ) )).

tff(u3646,axiom,
    ( ~ ! [X9,X10] :
          ( k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relset_1(X9,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
    | ! [X9,X10] :
        ( k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relset_1(X9,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) )).

tff(u3645,axiom,
    ( ~ ! [X3,X5,X2,X4] :
          ( k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X4,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )
    | ! [X3,X5,X2,X4] :
        ( k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X4,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ) )).

tff(u3644,axiom,
    ( ~ ! [X27,X29,X26,X28] :
          ( k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X26,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27))))
          | k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29))
          | k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X28,X29,sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) )
    | ! [X27,X29,X26,X28] :
        ( k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X26,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27))))
        | k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29))
        | k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X28,X29,sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) ) )).

tff(u3643,negated_conjecture,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

tff(u3642,axiom,
    ( ~ ! [X1,X0] : k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ! [X1,X0] : k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) )).

tff(u3641,axiom,
    ( ~ ! [X1,X0] : k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k2_relat_1(k2_zfmisc_1(X0,X1))
    | ! [X1,X0] : k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k2_relat_1(k2_zfmisc_1(X0,X1)) )).

tff(u3640,axiom,
    ( ~ ! [X5,X4] :
          ( k2_relset_1(X4,X5,sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
          | k1_xboole_0 = k2_zfmisc_1(X4,X5) )
    | ! [X5,X4] :
        ( k2_relset_1(X4,X5,sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
        | k1_xboole_0 = k2_zfmisc_1(X4,X5) ) )).

tff(u3639,axiom,
    ( ~ ! [X7,X6] :
          ( k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)) )
    | ! [X7,X6] :
        ( k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)) ) )).

tff(u3638,axiom,
    ( ~ ! [X22,X25,X23,X24] :
          ( k2_relset_1(X24,X25,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25)) )
    | ! [X22,X25,X23,X24] :
        ( k2_relset_1(X24,X25,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25)) ) )).

tff(u3637,axiom,
    ( ~ ! [X7,X8] :
          ( k2_relset_1(X7,X8,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
    | ! [X7,X8] :
        ( k2_relset_1(X7,X8,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) )).

tff(u3636,negated_conjecture,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2) )).

tff(u3635,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(X1,X0)
          | X0 = X1
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) ) )).

tff(u3634,axiom,
    ( ~ ! [X1] :
          ( ~ r1_tarski(X1,k1_xboole_0)
          | k1_xboole_0 = X1 )
    | ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) )).

tff(u3633,axiom,
    ( ~ ! [X0] :
          ( ~ r1_tarski(X0,k1_xboole_0)
          | v1_xboole_0(X0) )
    | ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) ) )).

tff(u3632,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X0))
          | v1_partfun1(X1,X2)
          | ~ v1_funct_2(X1,X2,X0)
          | ~ v1_funct_1(X1)
          | k1_xboole_0 = X0 )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X0))
        | v1_partfun1(X1,X2)
        | ~ v1_funct_2(X1,X2,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0 ) )).

tff(u3631,axiom,
    ( ~ ! [X3,X5,X2,X4] :
          ( ~ r1_tarski(X2,k2_zfmisc_1(X4,X5))
          | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
          | ~ r1_tarski(k2_relat_1(X2),X3) )
    | ! [X3,X5,X2,X4] :
        ( ~ r1_tarski(X2,k2_zfmisc_1(X4,X5))
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ r1_tarski(k2_relat_1(X2),X3) ) )).

tff(u3630,axiom,
    ( ~ ! [X3,X2,X4] :
          ( ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
          | ~ v1_funct_1(X2)
          | v1_funct_2(X2,X3,X4)
          | ~ v1_partfun1(X2,X3) )
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
        | ~ v1_funct_1(X2)
        | v1_funct_2(X2,X3,X4)
        | ~ v1_partfun1(X2,X3) ) )).

tff(u3629,axiom,
    ( ~ ! [X3,X2,X4] :
          ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
          | k2_relset_1(X2,X3,X4) = k2_relat_1(X4) )
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
        | k2_relset_1(X2,X3,X4) = k2_relat_1(X4) ) )).

tff(u3628,axiom,
    ( ~ ! [X1,X3,X2] :
          ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
          | v4_relat_1(X1,X2) )
    | ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
        | v4_relat_1(X1,X2) ) )).

tff(u3627,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
          | v1_relat_1(X0) )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
        | v1_relat_1(X0) ) )).

tff(u3626,axiom,
    ( ~ ! [X1,X2] :
          ( ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2))
          | ~ v1_funct_2(X1,k1_xboole_0,X2)
          | ~ v1_funct_1(X1)
          | v1_partfun1(X1,k1_xboole_0) )
    | ! [X1,X2] :
        ( ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2))
        | ~ v1_funct_2(X1,k1_xboole_0,X2)
        | ~ v1_funct_1(X1)
        | v1_partfun1(X1,k1_xboole_0) ) )).

tff(u3625,axiom,
    ( ~ ! [X2] :
          ( ~ r1_tarski(X2,sK3(k1_zfmisc_1(X2)))
          | sK3(k1_zfmisc_1(X2)) = X2
          | k1_xboole_0 = X2 )
    | ! [X2] :
        ( ~ r1_tarski(X2,sK3(k1_zfmisc_1(X2)))
        | sK3(k1_zfmisc_1(X2)) = X2
        | k1_xboole_0 = X2 ) )).

tff(u3624,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(X0,sK5(X0,X1))
          | k1_zfmisc_1(X0) = X1
          | sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) )
    | ! [X1,X0] :
        ( ~ r1_tarski(X0,sK5(X0,X1))
        | k1_zfmisc_1(X0) = X1
        | sK5(X0,X1) = X0
        | r2_hidden(sK5(X0,X1),X1) ) )).

tff(u3623,axiom,
    ( ~ ! [X0] :
          ( ~ r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0)))
          | k1_xboole_0 = sK5(X0,k1_zfmisc_1(k1_xboole_0))
          | sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )
    | ! [X0] :
        ( ~ r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0)))
        | k1_xboole_0 = sK5(X0,k1_zfmisc_1(k1_xboole_0))
        | sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u3622,axiom,
    ( ~ ! [X0] :
          ( ~ r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0)))
          | v1_xboole_0(sK5(X0,k1_zfmisc_1(k1_xboole_0)))
          | sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )
    | ! [X0] :
        ( ~ r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(sK5(X0,k1_zfmisc_1(k1_xboole_0)))
        | sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u3621,axiom,
    ( ~ ! [X1,X2] :
          ( ~ r1_tarski(X1,sK5(X1,k1_zfmisc_1(X2)))
          | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
          | sK5(X1,k1_zfmisc_1(X2)) = X1
          | r1_tarski(sK5(X1,k1_zfmisc_1(X2)),X2) )
    | ! [X1,X2] :
        ( ~ r1_tarski(X1,sK5(X1,k1_zfmisc_1(X2)))
        | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
        | sK5(X1,k1_zfmisc_1(X2)) = X1
        | r1_tarski(sK5(X1,k1_zfmisc_1(X2)),X2) ) )).

tff(u3620,axiom,
    ( ~ ! [X7,X8,X6] :
          ( ~ r1_tarski(X8,sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
          | k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X6,k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))),sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
          | sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) = X8
          | k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = k1_zfmisc_1(X8) )
    | ! [X7,X8,X6] :
        ( ~ r1_tarski(X8,sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
        | k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X6,k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))),sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
        | sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) = X8
        | k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = k1_zfmisc_1(X8) ) )).

tff(u3619,axiom,
    ( ~ ! [X3,X2,X4] :
          ( ~ r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k2_relset_1(X2,X3,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4
          | k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k2_relset_1(X2,X3,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4
        | k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ) )).

tff(u3618,axiom,
    ( ~ ! [X3,X2,X4] :
          ( ~ r1_tarski(X2,sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
          | k1_zfmisc_1(X2) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
          | sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = X2
          | v4_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) )
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))
        | k1_zfmisc_1(X2) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))
        | sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = X2
        | v4_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) ) )).

tff(u3617,axiom,
    ( ~ ! [X3,X2,X4] :
          ( ~ r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | v1_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4
          | k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | v1_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4
        | k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ) )).

tff(u3616,axiom,
    ( ~ ! [X3,X2] :
          ( ~ r1_tarski(X3,sK5(X2,k1_zfmisc_1(X3)))
          | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
          | sK5(X2,k1_zfmisc_1(X3)) = X3
          | r1_tarski(sK5(X2,k1_zfmisc_1(X3)),X2) )
    | ! [X3,X2] :
        ( ~ r1_tarski(X3,sK5(X2,k1_zfmisc_1(X3)))
        | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
        | sK5(X2,k1_zfmisc_1(X3)) = X3
        | r1_tarski(sK5(X2,k1_zfmisc_1(X3)),X2) ) )).

tff(u3615,axiom,
    ( ~ ! [X1] :
          ( ~ r1_tarski(X1,sK5(k1_xboole_0,k1_zfmisc_1(X1)))
          | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
          | sK5(k1_xboole_0,k1_zfmisc_1(X1)) = X1
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X1)) )
    | ! [X1] :
        ( ~ r1_tarski(X1,sK5(k1_xboole_0,k1_zfmisc_1(X1)))
        | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
        | sK5(k1_xboole_0,k1_zfmisc_1(X1)) = X1
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X1)) ) )).

tff(u3614,axiom,
    ( ~ ! [X0] :
          ( ~ r1_tarski(X0,sK5(k1_xboole_0,k1_zfmisc_1(X0)))
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
          | sK5(k1_xboole_0,k1_zfmisc_1(X0)) = X0
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0))) )
    | ! [X0] :
        ( ~ r1_tarski(X0,sK5(k1_xboole_0,k1_zfmisc_1(X0)))
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
        | sK5(k1_xboole_0,k1_zfmisc_1(X0)) = X0
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0))) ) )).

tff(u3613,axiom,
    ( ~ ! [X5,X7,X6] :
          ( ~ r1_tarski(X7,sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)))
          | k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))
          | sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)) = X7
          | k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) )
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X7,sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)))
        | k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))
        | sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)) = X7
        | k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) ) )).

tff(u3612,axiom,
    ( ~ ! [X3,X5,X4] :
          ( ~ r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
          | k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
          | sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3
          | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3) )
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
        | k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
        | sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3
        | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3) ) )).

tff(u3611,axiom,
    ( ~ ! [X3,X5,X4] :
          ( ~ r1_tarski(X5,sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)))
          | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(X5)
          | sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)) = X5
          | v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)),X3) )
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)))
        | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(X5)
        | sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)) = X5
        | v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)),X3) ) )).

tff(u3610,axiom,
    ( ~ ! [X3,X5,X4] :
          ( ~ r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
          | v1_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
          | sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3
          | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3) )
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
        | v1_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))
        | sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3
        | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3) ) )).

tff(u3609,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ r1_tarski(k2_relat_1(sK2),X3)
          | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),X3,sK2) )
    | ! [X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X3)
        | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),X3,sK2) ) )).

tff(u3608,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)))),X1)
          | k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1))) )
    | ! [X1,X0] :
        ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)))),X1)
        | k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1))) ) )).

tff(u3607,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),X1)
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),X1)
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) ) )).

tff(u3606,axiom,
    ( ~ ! [X5,X4,X6] :
          ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X4,X5)),X6)
          | ~ v1_partfun1(k2_zfmisc_1(X4,X5),X4)
          | ~ v1_funct_1(k2_zfmisc_1(X4,X5))
          | v1_funct_2(k2_zfmisc_1(X4,X5),X4,X6) )
    | ! [X5,X4,X6] :
        ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X4,X5)),X6)
        | ~ v1_partfun1(k2_zfmisc_1(X4,X5),X4)
        | ~ v1_funct_1(k2_zfmisc_1(X4,X5))
        | v1_funct_2(k2_zfmisc_1(X4,X5),X4,X6) ) )).

tff(u3605,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X2)),X1)
          | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X2)
          | k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,X2) )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X2)),X1)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X2)
        | k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,X2) ) )).

tff(u3604,axiom,
    ( ~ ! [X9,X7,X8] :
          ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X7,X8)),X9)
          | k2_relat_1(k2_zfmisc_1(X7,X8)) = k2_relset_1(X7,X9,k2_zfmisc_1(X7,X8)) )
    | ! [X9,X7,X8] :
        ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X7,X8)),X9)
        | k2_relat_1(k2_zfmisc_1(X7,X8)) = k2_relset_1(X7,X9,k2_zfmisc_1(X7,X8)) ) )).

tff(u3603,axiom,
    ( ~ ! [X9,X7,X8] :
          ( ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
          | k1_xboole_0 = k2_zfmisc_1(X7,X8)
          | ~ v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
          | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9) )
    | ! [X9,X7,X8] :
        ( ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
        | k1_xboole_0 = k2_zfmisc_1(X7,X8)
        | ~ v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
        | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9) ) )).

tff(u3602,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12)
          | k1_xboole_0 = k2_zfmisc_1(X10,X11)
          | k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )
    | ! [X11,X10,X12] :
        ( ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12)
        | k1_xboole_0 = k2_zfmisc_1(X10,X11)
        | k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) )).

tff(u3601,axiom,
    ( ~ ! [X9,X7,X8] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)))
          | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9) )
    | ! [X9,X7,X8] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)))
        | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9) ) )).

tff(u3600,axiom,
    ( ~ ! [X9,X7,X8] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
          | v1_xboole_0(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)))
          | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9) )
    | ! [X9,X7,X8] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
        | v1_xboole_0(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)))
        | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9) ) )).

tff(u3599,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))
          | k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X11,X10,X12] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))
        | k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3598,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
          | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
          | k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X11,X10,X12] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
        | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
        | k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3597,axiom,
    ( ~ ! [X5,X4,X6] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))),X6)
          | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X4,X6))
          | k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))) = k2_relset_1(X4,X6,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))) )
    | ! [X5,X4,X6] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))),X6)
        | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X4,X6))
        | k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))) = k2_relset_1(X4,X6,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))) ) )).

tff(u3596,axiom,
    ( ~ ! [X9,X7,X8] :
          ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
          | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
          | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9) )
    | ! [X9,X7,X8] :
        ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
        | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
        | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9) ) )).

tff(u3595,axiom,
    ( ~ ! [X9,X7,X8] :
          ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
          | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
          | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9) )
    | ! [X9,X7,X8] :
        ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))
        | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
        | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9) ) )).

tff(u3594,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12)
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
          | k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )
    | ! [X11,X10,X12] :
        ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12)
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
        | k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) )).

tff(u3593,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
          | k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )
    | ! [X11,X10,X12] :
        ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
        | k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) )).

tff(u3592,axiom,
    ( ~ ! [X11,X13,X12,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),X13)),X14)
          | m1_subset_1(sK5(k2_zfmisc_1(X11,X12),X13),k1_zfmisc_1(k2_zfmisc_1(X11,X14)))
          | r2_hidden(sK5(k2_zfmisc_1(X11,X12),X13),X13)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = X13 )
    | ! [X11,X13,X12,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),X13)),X14)
        | m1_subset_1(sK5(k2_zfmisc_1(X11,X12),X13),k1_zfmisc_1(k2_zfmisc_1(X11,X14)))
        | r2_hidden(sK5(k2_zfmisc_1(X11,X12),X13),X13)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = X13 ) )).

tff(u3591,axiom,
    ( ~ ! [X5,X7,X8,X6] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),X8)
          | k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))
          | m1_subset_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),k1_zfmisc_1(k2_zfmisc_1(X5,X8)))
          | r1_tarski(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),X7) )
    | ! [X5,X7,X8,X6] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),X8)
        | k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))
        | m1_subset_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),k1_zfmisc_1(k2_zfmisc_1(X5,X8)))
        | r1_tarski(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),X7) ) )).

tff(u3590,axiom,
    ( ~ ! [X9,X7,X8,X6] :
          ( ~ r1_tarski(k2_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
          | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X6)
          | m1_subset_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),k1_zfmisc_1(k2_zfmisc_1(X7,X9)))
          | r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6) )
    | ! [X9,X7,X8,X6] :
        ( ~ r1_tarski(k2_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9)
        | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X6)
        | m1_subset_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),k1_zfmisc_1(k2_zfmisc_1(X7,X9)))
        | r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6) ) )).

tff(u3589,axiom,
    ( ~ ! [X16,X13,X15,X17,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16)))),X17)
          | k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | m1_subset_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),k1_zfmisc_1(k2_zfmisc_1(X13,X17)))
          | v4_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),X15) )
    | ! [X16,X13,X15,X17,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16)))),X17)
        | k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | m1_subset_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),k1_zfmisc_1(k2_zfmisc_1(X13,X17)))
        | v4_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),X15) ) )).

tff(u3588,axiom,
    ( ~ ! [X16,X18,X15,X17,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X18)
          | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | m1_subset_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),k1_zfmisc_1(k2_zfmisc_1(X16,X18)))
          | v4_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),X14) )
    | ! [X16,X18,X15,X17,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X18)
        | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | m1_subset_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),k1_zfmisc_1(k2_zfmisc_1(X16,X18)))
        | v4_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),X14) ) )).

tff(u3587,axiom,
    ( ~ ! [X11,X13,X15,X12,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15) )
    | ! [X11,X13,X15,X12,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15) ) )).

tff(u3586,axiom,
    ( ~ ! [X16,X18,X20,X17,X19] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)
          | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) )
    | ! [X16,X18,X20,X17,X19] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)
        | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) ) )).

tff(u3585,axiom,
    ( ~ ! [X11,X13,X15,X12,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X11,X12,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13,X15) )
    | ! [X11,X13,X15,X12,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X11,X12,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13,X15) ) )).

tff(u3584,axiom,
    ( ~ ! [X16,X18,X20,X17,X19] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)
          | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) )
    | ! [X16,X18,X20,X17,X19] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)
        | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) ) )).

tff(u3583,axiom,
    ( ~ ! [X11,X13,X15,X12,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15) )
    | ! [X11,X13,X15,X12,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15) ) )).

tff(u3582,axiom,
    ( ~ ! [X16,X18,X20,X17,X19] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)
          | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) )
    | ! [X16,X18,X20,X17,X19] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)
        | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) ) )).

tff(u3581,axiom,
    ( ~ ! [X11,X13,X15,X12,X14] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),X15)
          | k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X15) )
    | ! [X11,X13,X15,X12,X14] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),X15)
        | k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X15) ) )).

tff(u3580,axiom,
    ( ~ ! [X16,X18,X20,X17,X19] :
          ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X20)
          | k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))
          | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) )
    | ! [X16,X18,X20,X17,X19] :
        ( ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X20)
        | k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))
        | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) ) )).

tff(u3579,negated_conjecture,
    ( ~ ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) )).

tff(u3578,negated_conjecture,
    ( ~ ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))
    | ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))) )).

tff(u3577,negated_conjecture,
    ( ~ ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))
    | ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) )).

tff(u3576,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(X1))
          | u1_struct_0(X1) = k1_relat_1(sK2)
          | ~ m1_yellow_0(X1,sK0) )
    | ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(X1))
        | u1_struct_0(X1) = k1_relat_1(sK2)
        | ~ m1_yellow_0(X1,sK0) ) )).

tff(u3575,axiom,
    ( ~ ! [X18,X20,X19] :
          ( ~ r1_tarski(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X18,X19))
          | k2_zfmisc_1(X18,X19) = k2_zfmisc_1(X18,X20)
          | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20) )
    | ! [X18,X20,X19] :
        ( ~ r1_tarski(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X18,X19))
        | k2_zfmisc_1(X18,X19) = k2_zfmisc_1(X18,X20)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20) ) )).

tff(u3574,negated_conjecture,
    ( ~ ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2) )).

tff(u3573,negated_conjecture,
    ( ~ ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),sK2)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),sK2) )).

tff(u3572,negated_conjecture,
    ( ~ ! [X4] :
          ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X4),sK2)
          | sK2 = k2_zfmisc_1(k1_relat_1(sK2),X4)
          | ~ r1_tarski(k2_relat_1(sK2),X4) )
    | ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X4),sK2)
        | sK2 = k2_zfmisc_1(k1_relat_1(sK2),X4)
        | ~ r1_tarski(k2_relat_1(sK2),X4) ) )).

tff(u3571,axiom,
    ( ~ ! [X22,X21,X23] :
          ( ~ r1_tarski(k2_zfmisc_1(X21,X23),sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))))
          | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)
          | sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))) = k2_zfmisc_1(X21,X23)
          | k1_xboole_0 = k2_zfmisc_1(X21,X22) )
    | ! [X22,X21,X23] :
        ( ~ r1_tarski(k2_zfmisc_1(X21,X23),sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))))
        | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)
        | sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))) = k2_zfmisc_1(X21,X23)
        | k1_xboole_0 = k2_zfmisc_1(X21,X22) ) )).

tff(u3570,axiom,
    ( ~ ! [X22,X21,X23] :
          ( ~ r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23))),sK5(k2_zfmisc_1(X21,X22),X23))
          | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23)
          | sK5(k2_zfmisc_1(X21,X22),X23) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23)))
          | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23 )
    | ! [X22,X21,X23] :
        ( ~ r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23))),sK5(k2_zfmisc_1(X21,X22),X23))
        | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23)
        | sK5(k2_zfmisc_1(X21,X22),X23) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23)))
        | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23 ) )).

tff(u3569,axiom,
    ( ~ ! [X22,X21,X23] :
          ( ~ r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)))
          | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23)
          | sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23))))
          | r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)),X23) )
    | ! [X22,X21,X23] :
        ( ~ r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)))
        | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23)
        | sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23))))
        | r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)),X23) ) )).

tff(u3568,axiom,
    ( ~ ! [X29,X31,X28,X30] :
          ( ~ r1_tarski(k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
          | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))
          | sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X30) )
    | ! [X29,X31,X28,X30] :
        ( ~ r1_tarski(k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
        | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))
        | sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X30) ) )).

tff(u3567,axiom,
    ( ~ ! [X22,X21,X23] :
          ( ~ r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
          | k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))
          | k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) )
    | ! [X22,X21,X23] :
        ( ~ r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
        | k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))
        | k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) ) )).

tff(u3566,axiom,
    ( ~ ! [X22,X21,X23] :
          ( ~ r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
          | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))
          | k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) )
    | ! [X22,X21,X23] :
        ( ~ r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
        | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))
        | k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) ) )).

tff(u3565,axiom,
    ( ~ ! [X42,X44,X46,X43,X45] :
          ( ~ r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
          | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)
          | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)) )
    | ! [X42,X44,X46,X43,X45] :
        ( ~ r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
        | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)
        | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)) ) )).

tff(u3564,axiom,
    ( ~ ! [X42,X44,X46,X43,X45] :
          ( ~ r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
          | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,X45,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)
          | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)) )
    | ! [X42,X44,X46,X43,X45] :
        ( ~ r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
        | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,X45,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)
        | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)) ) )).

tff(u3563,axiom,
    ( ~ ! [X29,X31,X28,X30] :
          ( ~ r1_tarski(k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
          | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))
          | sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28) )
    | ! [X29,X31,X28,X30] :
        ( ~ r1_tarski(k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
        | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))
        | sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28) ) )).

tff(u3562,axiom,
    ( ~ ! [X42,X44,X46,X43,X45] :
          ( ~ r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
          | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))
          | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)
          | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) )
    | ! [X42,X44,X46,X43,X45] :
        ( ~ r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
        | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))
        | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)
        | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) ) )).

tff(u3561,axiom,
    ( ~ ! [X42,X44,X46,X43,X45] :
          ( ~ r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
          | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,X43,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
          | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)
          | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)) )
    | ! [X42,X44,X46,X43,X45] :
        ( ~ r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46)
        | k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,X43,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))
        | sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)
        | k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)) ) )).

tff(u3560,axiom,
    ( ~ ! [X25,X23,X24] :
          ( ~ r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
          | sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
    | ! [X25,X23,X24] :
        ( ~ r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
        | sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) )).

tff(u3559,axiom,
    ( ~ ! [X25,X23,X24] :
          ( ~ r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
          | sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) )
    | ! [X25,X23,X24] :
        ( ~ r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
        | sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) ) )).

tff(u3558,axiom,
    ( ~ ! [X22,X21,X23] :
          ( ~ r1_tarski(k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))),sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21)
          | sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) = k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))
          | r1_tarski(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X21) )
    | ! [X22,X21,X23] :
        ( ~ r1_tarski(k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))),sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21)
        | sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) = k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))
        | r1_tarski(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X21) ) )).

tff(u3557,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ l1_orders_2(X1)
          | u1_struct_0(X0) = u1_struct_0(X1)
          | ~ m1_yellow_0(X0,X1) )
    | ! [X1,X0] :
        ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_orders_2(X1)
        | u1_struct_0(X0) = u1_struct_0(X1)
        | ~ m1_yellow_0(X0,X1) ) )).

tff(u3556,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(u1_struct_0(X0),k1_relat_1(sK2))
          | ~ l1_orders_2(X0)
          | u1_struct_0(X0) = k1_relat_1(sK2)
          | ~ m1_yellow_0(sK0,X0) )
    | ! [X0] :
        ( ~ r1_tarski(u1_struct_0(X0),k1_relat_1(sK2))
        | ~ l1_orders_2(X0)
        | u1_struct_0(X0) = k1_relat_1(sK2)
        | ~ m1_yellow_0(sK0,X0) ) )).

tff(u3555,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
          | m1_yellow_0(X1,X0)
          | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ l1_orders_2(X1)
          | ~ l1_orders_2(X0) )
    | ! [X1,X0] :
        ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
        | m1_yellow_0(X1,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(X0) ) )).

tff(u3554,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
          | ~ l1_orders_2(X1)
          | u1_orders_2(X1) = u1_orders_2(X0)
          | ~ m1_yellow_0(X0,X1) )
    | ! [X1,X0] :
        ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
        | ~ l1_orders_2(X1)
        | u1_orders_2(X1) = u1_orders_2(X0)
        | ~ m1_yellow_0(X0,X1) ) )).

tff(u3553,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) )).

tff(u3552,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1)
          | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
          | ~ r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0) )
    | ! [X1,X0] :
        ( ~ r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1)
        | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
        | ~ r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0) ) )).

tff(u3551,axiom,
    ( ~ ! [X5,X7,X6] :
          ( ~ r1_tarski(sK5(k2_zfmisc_1(X5,X6),X7),k2_zfmisc_1(X5,X6))
          | k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)),sK5(k2_zfmisc_1(X5,X6),X7))
          | k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7 )
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(sK5(k2_zfmisc_1(X5,X6),X7),k2_zfmisc_1(X5,X6))
        | k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)),sK5(k2_zfmisc_1(X5,X6),X7))
        | k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7 ) )).

tff(u3550,axiom,
    ( ~ ! [X1] : r1_tarski(X1,X1)
    | ! [X1] : r1_tarski(X1,X1) )).

tff(u3549,axiom,
    ( ~ ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u3548,axiom,
    ( ~ ! [X0] :
          ( r1_tarski(sK3(k1_zfmisc_1(X0)),X0)
          | k1_xboole_0 = X0 )
    | ! [X0] :
        ( r1_tarski(sK3(k1_zfmisc_1(X0)),X0)
        | k1_xboole_0 = X0 ) )).

tff(u3547,axiom,
    ( ~ ! [X2] :
          ( r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)
          | k1_xboole_0 = sK5(X2,k1_zfmisc_1(k1_xboole_0)) )
    | ! [X2] :
        ( r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)
        | k1_xboole_0 = sK5(X2,k1_zfmisc_1(k1_xboole_0)) ) )).

tff(u3546,axiom,
    ( ~ ! [X5] :
          ( r1_tarski(sK5(X5,k1_zfmisc_1(k1_xboole_0)),X5)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X5)
          | v1_xboole_0(sK5(X5,k1_zfmisc_1(k1_xboole_0))) )
    | ! [X5] :
        ( r1_tarski(sK5(X5,k1_zfmisc_1(k1_xboole_0)),X5)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X5)
        | v1_xboole_0(sK5(X5,k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3545,axiom,
    ( ~ ! [X11,X10,X12] :
          ( r1_tarski(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X12)
          | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(X12)
          | k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )
    | ! [X11,X10,X12] :
        ( r1_tarski(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X12)
        | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(X12)
        | k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) )).

tff(u3544,axiom,
    ( ~ ! [X13,X15,X14] :
          ( r1_tarski(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X13)
          | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(X13)
          | k2_relset_1(X14,X15,sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relat_1(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) )
    | ! [X13,X15,X14] :
        ( r1_tarski(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X13)
        | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(X13)
        | k2_relset_1(X14,X15,sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relat_1(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) ) )).

tff(u3543,axiom,
    ( ~ ! [X20,X19,X21] :
          ( r1_tarski(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X19)
          | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(X19)
          | v1_relat_1(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) )
    | ! [X20,X19,X21] :
        ( r1_tarski(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X19)
        | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(X19)
        | v1_relat_1(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) ) )).

tff(u3542,axiom,
    ( ~ ! [X0] :
          ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0)
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X0))
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )
    | ! [X0] :
        ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0)
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X0))
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u3541,axiom,
    ( ~ ! [X0] :
          ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0)))
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) )
    | ! [X0] :
        ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0)))
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u3540,axiom,
    ( ~ ! [X1,X0] :
          ( r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1)
          | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0)
          | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )
    | ! [X1,X0] :
        ( r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1)
        | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0)
        | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ) )).

tff(u3539,axiom,
    ( ~ ! [X1,X0,X2] :
          ( r1_tarski(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)),X2)
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) )
    | ! [X1,X0,X2] :
        ( r1_tarski(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)),X2)
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ) )).

tff(u3538,axiom,
    ( ~ ! [X13,X12,X14] :
          ( r1_tarski(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14)),X14)
          | k1_zfmisc_1(X14) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
          | k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))) )
    | ! [X13,X12,X14] :
        ( r1_tarski(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14)),X14)
        | k1_zfmisc_1(X14) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
        | k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))) ) )).

tff(u3537,axiom,
    ( ~ ! [X18,X20,X19] :
          ( r1_tarski(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20)),X20)
          | k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
          | v1_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20))) )
    | ! [X18,X20,X19] :
        ( r1_tarski(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20)),X20)
        | k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
        | v1_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20))) ) )).

tff(u3536,negated_conjecture,
    ( ~ ! [X2] :
          ( r1_tarski(u1_struct_0(X2),k1_relat_1(sK2))
          | ~ m1_yellow_0(X2,sK0) )
    | ! [X2] :
        ( r1_tarski(u1_struct_0(X2),k1_relat_1(sK2))
        | ~ m1_yellow_0(X2,sK0) ) )).

tff(u3535,axiom,
    ( ~ ! [X18,X20,X19] :
          ( r1_tarski(k2_zfmisc_1(X18,X19),k2_zfmisc_1(X18,X20))
          | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20) )
    | ! [X18,X20,X19] :
        ( r1_tarski(k2_zfmisc_1(X18,X19),k2_zfmisc_1(X18,X20))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20) ) )).

tff(u3534,negated_conjecture,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) )).

tff(u3533,negated_conjecture,
    ( ~ ! [X6] :
          ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X6))
          | ~ r1_tarski(k2_relat_1(sK2),X6) )
    | ! [X6] :
        ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X6))
        | ~ r1_tarski(k2_relat_1(sK2),X6) ) )).

tff(u3532,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23))
          | k1_xboole_0 = k2_zfmisc_1(X21,X22)
          | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23))
        | k1_xboole_0 = k2_zfmisc_1(X21,X22)
        | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) ) )).

tff(u3531,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(k2_zfmisc_1(X21,X22),X23),k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23))))
          | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23
          | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(k2_zfmisc_1(X21,X22),X23),k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23))))
        | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23
        | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23) ) )).

tff(u3530,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),k2_zfmisc_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)))))
          | r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),X21)
          | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),k2_zfmisc_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)))))
        | r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),X21)
        | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21) ) )).

tff(u3529,axiom,
    ( ~ ! [X29,X31,X28,X30] :
          ( r1_tarski(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))
          | v4_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28)
          | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31)) )
    | ! [X29,X31,X28,X30] :
        ( r1_tarski(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))
        | v4_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28)
        | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31)) ) )).

tff(u3528,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
          | k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
        | k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)) ) )).

tff(u3527,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
          | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23)
        | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3526,axiom,
    ( ~ ! [X36,X38,X35,X37,X39] :
          ( r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39))
          | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39)
          | k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) )
    | ! [X36,X38,X35,X37,X39] :
        ( r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39))
        | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39)
        | k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) ) )).

tff(u3525,axiom,
    ( ~ ! [X36,X38,X35,X37,X39] :
          ( r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39))
          | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39)
          | k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,X38,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) )
    | ! [X36,X38,X35,X37,X39] :
        ( r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39))
        | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39)
        | k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,X38,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) ) )).

tff(u3524,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) ) )).

tff(u3523,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23))
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23))
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)) ) )).

tff(u3522,axiom,
    ( ~ ! [X22,X21,X23] :
          ( r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,k2_relat_1(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))
          | r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X23)
          | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23) )
    | ! [X22,X21,X23] :
        ( r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,k2_relat_1(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))
        | r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X23)
        | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23) ) )).

tff(u3521,axiom,
    ( ~ ! [X29,X31,X28,X30] :
          ( r1_tarski(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))
          | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28)
          | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31)) )
    | ! [X29,X31,X28,X30] :
        ( r1_tarski(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))
        | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28)
        | k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31)) ) )).

tff(u3520,axiom,
    ( ~ ! [X36,X38,X35,X37,X39] :
          ( r1_tarski(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k2_zfmisc_1(X35,X39))
          | k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),X39)
          | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38)) )
    | ! [X36,X38,X35,X37,X39] :
        ( r1_tarski(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k2_zfmisc_1(X35,X39))
        | k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),X39)
        | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38)) ) )).

tff(u3519,axiom,
    ( ~ ! [X36,X38,X35,X37,X39] :
          ( r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X37,X39))
          | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39)
          | k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X35,X36,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) )
    | ! [X36,X38,X35,X37,X39] :
        ( r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X37,X39))
        | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39)
        | k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X35,X36,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) ) )).

tff(u3518,axiom,
    ( ~ ! [X1,X0] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_yellow_0(X1,X0)
          | ~ l1_orders_2(X0) )
    | ! [X1,X0] :
        ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_yellow_0(X1,X0)
        | ~ l1_orders_2(X0) ) )).

tff(u3517,negated_conjecture,
    ( ~ ! [X3] :
          ( r1_tarski(k1_relat_1(sK2),u1_struct_0(X3))
          | ~ m1_yellow_0(sK0,X3)
          | ~ l1_orders_2(X3) )
    | ! [X3] :
        ( r1_tarski(k1_relat_1(sK2),u1_struct_0(X3))
        | ~ m1_yellow_0(sK0,X3)
        | ~ l1_orders_2(X3) ) )).

tff(u3516,axiom,
    ( ~ ! [X1,X0] :
          ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
          | ~ m1_yellow_0(X1,X0)
          | ~ l1_orders_2(X0) )
    | ! [X1,X0] :
        ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
        | ~ m1_yellow_0(X1,X0)
        | ~ l1_orders_2(X0) ) )).

tff(u3515,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r1_tarski(X1,X0)
          | v1_xboole_0(X1) )
    | ! [X1,X0] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) ) )).

tff(u3514,axiom,
    ( ~ ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

tff(u3513,axiom,
    ( ~ ! [X0] :
          ( ~ v1_xboole_0(u1_struct_0(X0))
          | ~ l1_struct_0(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) )).

tff(u3512,negated_conjecture,
    ( ~ ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(sK2)) )).

tff(u3511,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u3510,axiom,
    ( ~ ! [X13,X12] :
          ( v1_xboole_0(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
          | k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X13,X12] :
        ( v1_xboole_0(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
        | k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3509,axiom,
    ( ~ ! [X7,X6] :
          ( v1_xboole_0(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))
          | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X7,X6] :
        ( v1_xboole_0(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))
        | k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3508,axiom,
    ( ~ ! [X11,X12] :
          ( v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X11,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12)) )
    | ! [X11,X12] :
        ( v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X11,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12)) ) )).

tff(u3507,axiom,
    ( ~ ! [X7,X6] :
          ( v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))
          | k2_relset_1(X6,X7,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )
    | ! [X7,X6] :
        ( v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))
        | k2_relset_1(X6,X7,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) )).

tff(u3506,axiom,
    ( ~ ! [X3,X0] :
          ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
          | r1_tarski(X3,X0) )
    | ! [X3,X0] :
        ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
        | r1_tarski(X3,X0) ) )).

tff(u3505,axiom,
    ( ~ ! [X0] :
          ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
          | k1_xboole_0 = X0 )
    | ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) )).

tff(u3504,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r1_tarski(sK5(X0,X1),X0)
          | k1_zfmisc_1(X0) = X1 )
    | ! [X1,X0] :
        ( ~ r2_hidden(sK5(X0,X1),X1)
        | ~ r1_tarski(sK5(X0,X1),X0)
        | k1_zfmisc_1(X0) = X1 ) )).

tff(u3503,axiom,
    ( ~ ! [X3,X0] :
          ( r2_hidden(X3,k1_zfmisc_1(X0))
          | ~ r1_tarski(X3,X0) )
    | ! [X3,X0] :
        ( r2_hidden(X3,k1_zfmisc_1(X0))
        | ~ r1_tarski(X3,X0) ) )).

tff(u3502,axiom,
    ( ~ ! [X0] :
          ( r2_hidden(sK3(X0),X0)
          | k1_xboole_0 = k3_tarski(X0) )
    | ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = k3_tarski(X0) ) )).

tff(u3501,axiom,
    ( ~ ! [X1,X0] :
          ( r2_hidden(sK5(X0,X1),X1)
          | r1_tarski(sK5(X0,X1),X0)
          | k1_zfmisc_1(X0) = X1 )
    | ! [X1,X0] :
        ( r2_hidden(sK5(X0,X1),X1)
        | r1_tarski(sK5(X0,X1),X0)
        | k1_zfmisc_1(X0) = X1 ) )).

tff(u3500,axiom,
    ( ~ ! [X2] :
          ( r2_hidden(sK5(k1_xboole_0,X2),X2)
          | k1_zfmisc_1(k1_xboole_0) = X2
          | k1_xboole_0 = sK5(k1_xboole_0,X2) )
    | ! [X2] :
        ( r2_hidden(sK5(k1_xboole_0,X2),X2)
        | k1_zfmisc_1(k1_xboole_0) = X2
        | k1_xboole_0 = sK5(k1_xboole_0,X2) ) )).

tff(u3499,axiom,
    ( ~ ! [X3] :
          ( r2_hidden(sK5(k1_xboole_0,X3),X3)
          | k1_zfmisc_1(k1_xboole_0) = X3
          | v1_xboole_0(sK5(k1_xboole_0,X3)) )
    | ! [X3] :
        ( r2_hidden(sK5(k1_xboole_0,X3),X3)
        | k1_zfmisc_1(k1_xboole_0) = X3
        | v1_xboole_0(sK5(k1_xboole_0,X3)) ) )).

tff(u3498,axiom,
    ( ~ ! [X11,X10,X12] :
          ( r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12)
          | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12
          | k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)) = k2_relset_1(X10,k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)),sK5(k2_zfmisc_1(X10,X11),X12)) )
    | ! [X11,X10,X12] :
        ( r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12)
        | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12
        | k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)) = k2_relset_1(X10,k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)),sK5(k2_zfmisc_1(X10,X11),X12)) ) )).

tff(u3497,axiom,
    ( ~ ! [X5,X4,X6] :
          ( r2_hidden(sK5(k2_zfmisc_1(X4,X5),X6),X6)
          | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = X6
          | k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),X6)) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),X6)) )
    | ! [X5,X4,X6] :
        ( r2_hidden(sK5(k2_zfmisc_1(X4,X5),X6),X6)
        | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = X6
        | k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),X6)) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),X6)) ) )).

tff(u3496,axiom,
    ( ~ ! [X11,X10,X12] :
          ( r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12)
          | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12
          | v1_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)) )
    | ! [X11,X10,X12] :
        ( r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12)
        | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12
        | v1_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)) ) )).

tff(u3495,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
          | r1_tarski(X0,X1) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) ) )).

tff(u3494,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | k1_xboole_0 = X1
          | v1_partfun1(X2,X0)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(X2,X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) ) )).

tff(u3493,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X3),X1)
          | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ r1_tarski(k2_relat_1(X3),X1)
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) )).

tff(u3492,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | v1_funct_2(X2,X0,X1) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(X2,X0)
        | ~ v1_funct_1(X2)
        | v1_funct_2(X2,X0,X1) ) )).

tff(u3491,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) )).

tff(u3490,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | v4_relat_1(X2,X0) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) )).

tff(u3489,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | v1_relat_1(X2) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) )).

tff(u3488,axiom,
    ( ~ ! [X1,X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
          | v1_partfun1(X2,k1_xboole_0)
          | ~ v1_funct_2(X2,k1_xboole_0,X1)
          | ~ v1_funct_1(X2) )
    | ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_partfun1(X2,k1_xboole_0)
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ v1_funct_1(X2) ) )).

tff(u3487,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) )).

tff(u3486,negated_conjecture,
    ( ~ ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) )).

tff(u3485,negated_conjecture,
    ( ~ ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) )).

tff(u3484,axiom,
    ( ~ ! [X1,X0] :
          ( m1_subset_1(X0,k1_zfmisc_1(X1))
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) )).

tff(u3483,axiom,
    ( ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u3482,axiom,
    ( ~ ! [X3,X5,X4] :
          ( m1_subset_1(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
          | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X3,X4)),X5) )
    | ! [X3,X5,X4] :
        ( m1_subset_1(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X3,X4)),X5) ) )).

tff(u3481,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

tff(u3480,negated_conjecture,
    ( ~ ! [X6] :
          ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X6)))
          | ~ r1_tarski(k2_relat_1(sK2),X6) )
    | ! [X6] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X6)))
        | ~ r1_tarski(k2_relat_1(sK2),X6) ) )).

tff(u3479,axiom,
    ( ~ ! [X9,X8,X10] :
          ( m1_subset_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),k1_zfmisc_1(k2_zfmisc_1(X8,X10)))
          | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))),X10)
          | k1_xboole_0 = k2_zfmisc_1(X8,X9) )
    | ! [X9,X8,X10] :
        ( m1_subset_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),k1_zfmisc_1(k2_zfmisc_1(X8,X10)))
        | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))),X10)
        | k1_xboole_0 = k2_zfmisc_1(X8,X9) ) )).

tff(u3478,axiom,
    ( ~ ! [X1,X0,X2] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2)))))
          | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2 )
    | ! [X1,X0,X2] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2)))))
        | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2 ) )).

tff(u3477,axiom,
    ( ~ ! [X1,X3,X2] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3) )
    | ! [X1,X3,X2] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3) ) )).

tff(u3476,axiom,
    ( ~ ! [X1,X3,X2] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          | v1_xboole_0(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3) )
    | ! [X1,X3,X2] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3) ) )).

tff(u3475,axiom,
    ( ~ ! [X1,X0,X2] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))))))
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
          | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0) )
    | ! [X1,X0,X2] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))))))
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
        | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0) ) )).

tff(u3474,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) )
    | ! [X1,X3,X0,X2] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) ) )).

tff(u3473,axiom,
    ( ~ ! [X18,X20,X17,X19,X21] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))),k1_zfmisc_1(k2_zfmisc_1(X19,X21)))
          | k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))) = k2_relset_1(X17,k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))))
          | k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(k2_zfmisc_1(X19,X20))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),X21) )
    | ! [X18,X20,X17,X19,X21] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))),k1_zfmisc_1(k2_zfmisc_1(X19,X21)))
        | k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))) = k2_relset_1(X17,k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))))
        | k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(k2_zfmisc_1(X19,X20))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),X21) ) )).

tff(u3472,axiom,
    ( ~ ! [X16,X13,X15,X17,X14] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),k1_zfmisc_1(k2_zfmisc_1(X15,X17)))
          | k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X17) )
    | ! [X16,X13,X15,X17,X14] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),k1_zfmisc_1(k2_zfmisc_1(X15,X17)))
        | k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X17) ) )).

tff(u3471,axiom,
    ( ~ ! [X3,X2,X4] :
          ( m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) )
    | ! [X3,X2,X4] :
        ( m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) ) )).

tff(u3470,axiom,
    ( ~ ! [X1,X3,X2] :
          ( m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3) )
    | ! [X1,X3,X2] :
        ( m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3) ) )).

tff(u3469,axiom,
    ( ~ ! [X1,X0,X2] :
          ( m1_subset_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
          | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) )
    | ! [X1,X0,X2] :
        ( m1_subset_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
        | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) ) )).

tff(u3468,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) )
    | ! [X1,X3,X0,X2] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) ) )).

tff(u3467,axiom,
    ( ~ ! [X16,X18,X20,X17,X19] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
          | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) )
    | ! [X16,X18,X20,X17,X19] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
        | k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) ) )).

tff(u3466,axiom,
    ( ~ ! [X16,X18,X15,X17,X14] :
          ( m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),k1_zfmisc_1(k2_zfmisc_1(X14,X18)))
          | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
          | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),X18) )
    | ! [X16,X18,X15,X17,X14] :
        ( m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),k1_zfmisc_1(k2_zfmisc_1(X14,X18)))
        | k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
        | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),X18) ) )).

tff(u3465,axiom,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) )).

tff(u3464,axiom,
    ( ~ ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) )).

tff(u3463,negated_conjecture,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(sK2) )).

tff(u3462,axiom,
    ( ~ ! [X1,X0] :
          ( v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ! [X1,X0] :
        ( v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )).

tff(u3461,axiom,
    ( ~ ! [X11,X10] :
          ( v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)) )
    | ! [X11,X10] :
        ( v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)) ) )).

tff(u3460,axiom,
    ( ~ ! [X11,X10] :
          ( v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
          | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)) )
    | ! [X11,X10] :
        ( v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)) ) )).

tff(u3459,axiom,
    ( ~ ! [X32,X31,X33,X30] :
          ( v1_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
          | k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33)) )
    | ! [X32,X31,X33,X30] :
        ( v1_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
        | k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33)) ) )).

tff(u3458,axiom,
    ( ~ ! [X11,X12] :
          ( v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
    | ! [X11,X12] :
        ( v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) )).

tff(u3457,axiom,
    ( ~ ! [X11,X10] :
          ( v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )
    | ! [X11,X10] :
        ( v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) )).

tff(u3456,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

tff(u3455,axiom,
    ( ~ ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) )).

tff(u3454,negated_conjecture,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(sK2) )).

tff(u3453,axiom,
    ( ~ ! [X1] :
          ( ~ v4_relat_1(X1,k1_relat_1(X1))
          | v1_partfun1(X1,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
    | ! [X1] :
        ( ~ v4_relat_1(X1,k1_relat_1(X1))
        | v1_partfun1(X1,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) )).

tff(u3452,axiom,
    ( ~ ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ! [X0] : v4_relat_1(k1_xboole_0,X0) )).

tff(u3451,axiom,
    ( ~ ! [X1,X0] : v4_relat_1(k2_zfmisc_1(X0,X1),X0)
    | ! [X1,X0] : v4_relat_1(k2_zfmisc_1(X0,X1),X0) )).

tff(u3450,negated_conjecture,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | v4_relat_1(sK2,k1_relat_1(sK2)) )).

tff(u3449,axiom,
    ( ~ ! [X3,X4] :
          ( v4_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
          | k1_xboole_0 = k2_zfmisc_1(X3,X4) )
    | ! [X3,X4] :
        ( v4_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)
        | k1_xboole_0 = k2_zfmisc_1(X3,X4) ) )).

tff(u3448,axiom,
    ( ~ ! [X9,X7,X8] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X7,X8),X9),X7)
          | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9)
          | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9 )
    | ! [X9,X7,X8] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X7,X8),X9),X7)
        | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9)
        | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9 ) )).

tff(u3447,axiom,
    ( ~ ! [X9,X8] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8)
          | k1_xboole_0 = sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9)) )
    | ! [X9,X8] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8)
        | k1_xboole_0 = sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9)) ) )).

tff(u3446,axiom,
    ( ~ ! [X9,X8] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8)
          | v1_xboole_0(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9)) )
    | ! [X9,X8] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8)
        | v1_xboole_0(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9)) ) )).

tff(u3445,axiom,
    ( ~ ! [X16,X15,X17] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X15)
          | r1_tarski(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X17)
          | k1_zfmisc_1(X17) = k1_zfmisc_1(k2_zfmisc_1(X15,X16)) )
    | ! [X16,X15,X17] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X15)
        | r1_tarski(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X17)
        | k1_zfmisc_1(X17) = k1_zfmisc_1(k2_zfmisc_1(X15,X16)) ) )).

tff(u3444,axiom,
    ( ~ ! [X32,X31,X33,X30] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X32)
          | k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) = k2_relset_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
          | k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33)) )
    | ! [X32,X31,X33,X30] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X32)
        | k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) = k2_relset_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))
        | k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33)) ) )).

tff(u3443,axiom,
    ( ~ ! [X25,X23,X24,X26] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X23)
          | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
          | k2_relset_1(X25,X26,sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) = k2_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) )
    | ! [X25,X23,X24,X26] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X23)
        | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
        | k2_relset_1(X25,X26,sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) = k2_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) ) )).

tff(u3442,axiom,
    ( ~ ! [X1,X0,X2] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))),X0)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) )
    | ! [X1,X0,X2] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))),X0)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)) ) )).

tff(u3441,axiom,
    ( ~ ! [X9,X10] :
          ( v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
    | ! [X9,X10] :
        ( v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) )).

tff(u3440,axiom,
    ( ~ ! [X9,X8] :
          ( v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9))
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) )
    | ! [X9,X8] :
        ( v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9))
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) ) )).

tff(u3439,axiom,
    ( ~ ! [X16,X18,X17] :
          ( v4_relat_1(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X17)
          | r1_tarski(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X16)
          | k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(X16) )
    | ! [X16,X18,X17] :
        ( v4_relat_1(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X17)
        | r1_tarski(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X16)
        | k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(X16) ) )).

tff(u3438,axiom,
    ( ~ ! [X18,X20,X19,X21] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20)
          | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
          | k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) )
    | ! [X18,X20,X19,X21] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20)
        | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
        | k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) ) )).

tff(u3437,axiom,
    ( ~ ! [X22,X25,X23,X24] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X24)
          | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))
          | k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))) = k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))) )
    | ! [X22,X25,X23,X24] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X24)
        | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))
        | k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))) = k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))) ) )).

tff(u3436,axiom,
    ( ~ ! [X27,X29,X26,X28] :
          ( v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28)
          | v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X26)
          | k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29)) )
    | ! [X27,X29,X26,X28] :
        ( v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28)
        | v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X26)
        | k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29)) ) )).

tff(u3435,axiom,
    ( ~ ! [X1,X0] :
          ( ~ v1_partfun1(X1,X0)
          | k1_relat_1(X1) = X0
          | ~ v4_relat_1(X1,X0)
          | ~ v1_relat_1(X1) )
    | ! [X1,X0] :
        ( ~ v1_partfun1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) )).

tff(u3434,axiom,
    ( ~ ! [X7,X8,X6] :
          ( ~ v1_partfun1(sK5(k2_zfmisc_1(X6,X7),X8),X6)
          | v1_funct_2(sK5(k2_zfmisc_1(X6,X7),X8),X6,X7)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X6,X7),X8))
          | r2_hidden(sK5(k2_zfmisc_1(X6,X7),X8),X8)
          | k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = X8 )
    | ! [X7,X8,X6] :
        ( ~ v1_partfun1(sK5(k2_zfmisc_1(X6,X7),X8),X6)
        | v1_funct_2(sK5(k2_zfmisc_1(X6,X7),X8),X6,X7)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X6,X7),X8))
        | r2_hidden(sK5(k2_zfmisc_1(X6,X7),X8),X8)
        | k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = X8 ) )).

tff(u3433,axiom,
    ( ~ ! [X9,X11,X10] :
          ( ~ v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9)
          | k1_zfmisc_1(X11) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)))
          | v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9,X10)
          | r1_tarski(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X11) )
    | ! [X9,X11,X10] :
        ( ~ v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9)
        | k1_zfmisc_1(X11) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)))
        | v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9,X10)
        | r1_tarski(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X11) ) )).

tff(u3432,axiom,
    ( ~ ! [X18,X20,X19,X21] :
          ( ~ v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18)
          | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))))
          | v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18,X19)
          | v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20) )
    | ! [X18,X20,X19,X21] :
        ( ~ v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18)
        | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))))
        | v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18,X19)
        | v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20) ) )).

tff(u3431,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ v1_partfun1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(X10)
          | ~ v1_funct_1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | v1_funct_2(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X12)
          | r1_tarski(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X10) )
    | ! [X11,X10,X12] :
        ( ~ v1_partfun1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(X10)
        | ~ v1_funct_1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | v1_funct_2(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X12)
        | r1_tarski(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X10) ) )).

tff(u3430,axiom,
    ( ~ ! [X20,X22,X19,X21] :
          ( ~ v1_partfun1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21)
          | k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))))
          | v1_funct_2(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21,X22)
          | v4_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X19) )
    | ! [X20,X22,X19,X21] :
        ( ~ v1_partfun1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21)
        | k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))))
        | v1_funct_2(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21,X22)
        | v4_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X19) ) )).

tff(u3429,axiom,
    ( ~ v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) )).

tff(u3428,negated_conjecture,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_partfun1(sK2,k1_relat_1(sK2)) )).

tff(u3427,negated_conjecture,
    ( ~ ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) )).

tff(u3426,negated_conjecture,
    ( ~ ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) )).

tff(u3425,axiom,
    ( ~ ! [X0] :
          ( ~ v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0)
          | ~ v1_funct_1(k2_zfmisc_1(k1_xboole_0,X0))
          | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) )
    | ! [X0] :
        ( ~ v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0)
        | ~ v1_funct_1(k2_zfmisc_1(k1_xboole_0,X0))
        | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) ) )).

tff(u3424,axiom,
    ( ~ ! [X16,X17] :
          ( ~ v1_funct_2(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0,X17)
          | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0)
          | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(k1_xboole_0,X16)),X17)
          | ~ v1_funct_1(k2_zfmisc_1(k1_xboole_0,X16)) )
    | ! [X16,X17] :
        ( ~ v1_funct_2(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0,X17)
        | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(k1_xboole_0,X16)),X17)
        | ~ v1_funct_1(k2_zfmisc_1(k1_xboole_0,X16)) ) )).

tff(u3423,axiom,
    ( ~ ! [X5,X4] :
          ( ~ v1_funct_2(k2_zfmisc_1(X4,X5),X4,X5)
          | v1_partfun1(k2_zfmisc_1(X4,X5),X4)
          | ~ v1_funct_1(k2_zfmisc_1(X4,X5))
          | k1_xboole_0 = X5 )
    | ! [X5,X4] :
        ( ~ v1_funct_2(k2_zfmisc_1(X4,X5),X4,X5)
        | v1_partfun1(k2_zfmisc_1(X4,X5),X4)
        | ~ v1_funct_1(k2_zfmisc_1(X4,X5))
        | k1_xboole_0 = X5 ) )).

tff(u3422,axiom,
    ( ~ ! [X5,X7,X6] :
          ( ~ v1_funct_2(k2_zfmisc_1(X6,X7),X6,X5)
          | v1_partfun1(k2_zfmisc_1(X6,X7),X6)
          | k1_xboole_0 = X5
          | ~ v1_funct_1(k2_zfmisc_1(X6,X7))
          | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X6,X7)),X5) )
    | ! [X5,X7,X6] :
        ( ~ v1_funct_2(k2_zfmisc_1(X6,X7),X6,X5)
        | v1_partfun1(k2_zfmisc_1(X6,X7),X6)
        | k1_xboole_0 = X5
        | ~ v1_funct_1(k2_zfmisc_1(X6,X7))
        | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X6,X7)),X5) ) )).

tff(u3421,negated_conjecture,
    ( ~ ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) )).

tff(u3420,axiom,
    ( ~ ! [X2] :
          ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0,X2)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))))
          | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0)
          | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) )
    | ! [X2] :
        ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0,X2)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))))
        | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0)
        | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ) )).

tff(u3419,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20)
          | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X19)
          | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
          | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20)
        | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X19)
        | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) ) )).

tff(u3418,axiom,
    ( ~ ! [X9,X8] :
          ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8,X9)
          | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))))
          | k1_xboole_0 = X9
          | k1_xboole_0 = k2_zfmisc_1(X8,X9) )
    | ! [X9,X8] :
        ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8,X9)
        | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))))
        | k1_xboole_0 = X9
        | k1_xboole_0 = k2_zfmisc_1(X8,X9) ) )).

tff(u3417,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2)
          | k1_xboole_0 = k2_zfmisc_1(X0,X1)
          | k1_xboole_0 = X2
          | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | k1_xboole_0 = X2
        | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | ~ r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3416,axiom,
    ( ~ ! [X3,X4] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0,X3)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0)
          | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),X4)
          | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)) = X4 )
    | ! [X3,X4] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0,X3)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0)
        | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),X4)
        | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)) = X4 ) )).

tff(u3415,axiom,
    ( ~ ! [X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12)
          | k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) )
    | ! [X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12)
        | k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ) )).

tff(u3414,axiom,
    ( ~ ! [X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12)
          | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) )
    | ! [X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12)
        | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ) )).

tff(u3413,axiom,
    ( ~ ! [X22,X21] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0,X21)
          | k1_zfmisc_1(X22) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X21))
          | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),X22)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0) )
    | ! [X22,X21] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0,X21)
        | k1_zfmisc_1(X22) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X21))
        | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),X22)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0) ) )).

tff(u3412,axiom,
    ( ~ ! [X40,X38,X39] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0,X40)
          | k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))) = k2_relset_1(X38,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))),sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))))
          | k1_zfmisc_1(k2_zfmisc_1(X38,X39)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X40))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0) )
    | ! [X40,X38,X39] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0,X40)
        | k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))) = k2_relset_1(X38,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))),sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))))
        | k1_zfmisc_1(k2_zfmisc_1(X38,X39)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X40))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0) ) )).

tff(u3411,axiom,
    ( ~ ! [X34,X36,X35] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36)
          | k2_relset_1(X34,X35,sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
          | k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0) )
    | ! [X34,X36,X35] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36)
        | k2_relset_1(X34,X35,sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
        | k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0) ) )).

tff(u3410,axiom,
    ( ~ ! [X34,X36,X35] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0,X34)
          | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X34))
          | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),X35)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0) )
    | ! [X34,X36,X35] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0,X34)
        | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X34))
        | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),X35)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0) ) )).

tff(u3409,axiom,
    ( ~ ! [X34,X36,X35] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36)
          | v1_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
          | k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0) )
    | ! [X34,X36,X35] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36)
        | v1_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
        | k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0) ) )).

tff(u3408,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20)
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
          | k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20)
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3407,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20)
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
          | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20)
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
        | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3406,axiom,
    ( ~ ! [X32,X34,X31,X33] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34)
          | k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34)
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0)
          | k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) )
    | ! [X32,X34,X31,X33] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34)
        | k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34)
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0)
        | k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) ) )).

tff(u3405,axiom,
    ( ~ ! [X32,X34,X31,X33] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34)
          | k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34)
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0)
          | k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,X33,sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) )
    | ! [X32,X34,X31,X33] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34)
        | k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34)
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0)
        | k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,X33,sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) ) )).

tff(u3404,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20)))
          | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)) = X20
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0)
          | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),X20)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20)) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20)))
        | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)) = X20
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0)
        | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),X20)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20)) ) )).

tff(u3403,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19))))
          | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),X19)
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0)
          | k1_zfmisc_1(X19) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X20))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19))))
        | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),X19)
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0)
        | k1_zfmisc_1(X19) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X20))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19))) ) )).

tff(u3402,axiom,
    ( ~ ! [X25,X27,X26] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))
          | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25)
          | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0)
          | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) )
    | ! [X25,X27,X26] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))
        | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25)
        | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0)
        | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) ) )).

tff(u3401,axiom,
    ( ~ ! [X38,X37,X39] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0,X39)
          | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
          | k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))))
          | v1_partfun1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0) )
    | ! [X38,X37,X39] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0,X39)
        | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))
        | k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))))
        | v1_partfun1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0) ) )).

tff(u3400,axiom,
    ( ~ ! [X36,X35,X37] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0,X35)
          | k2_relset_1(X36,X37,sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))))
          | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)) = k1_zfmisc_1(k2_zfmisc_1(X36,X37))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))))
          | v1_partfun1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0) )
    | ! [X36,X35,X37] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0,X35)
        | k2_relset_1(X36,X37,sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))))
        | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)) = k1_zfmisc_1(k2_zfmisc_1(X36,X37))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))))
        | v1_partfun1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0) ) )).

tff(u3399,axiom,
    ( ~ ! [X36,X35,X37] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0,X37)
          | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))
          | v4_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),X35)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))))
          | v1_partfun1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0) )
    | ! [X36,X35,X37] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0,X37)
        | k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))
        | v4_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),X35)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))))
        | v1_partfun1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0) ) )).

tff(u3398,axiom,
    ( ~ ! [X25,X27,X26] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),X25)
          | v1_partfun1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0)
          | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27)))) )
    | ! [X25,X27,X26] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),X25)
        | v1_partfun1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0)
        | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27)))) ) )).

tff(u3397,axiom,
    ( ~ ! [X32,X34,X31,X33] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0,X34)
          | k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),X34)
          | v1_partfun1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0)
          | k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))) )
    | ! [X32,X34,X31,X33] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0,X34)
        | k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),X34)
        | v1_partfun1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0)
        | k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))) ) )).

tff(u3396,axiom,
    ( ~ ! [X32,X34,X31,X33] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0,X34)
          | k1_zfmisc_1(k2_zfmisc_1(X31,X32)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))),X34)
          | v1_partfun1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0)
          | k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))) = k2_relset_1(X31,X32,sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))) )
    | ! [X32,X34,X31,X33] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0,X34)
        | k1_zfmisc_1(k2_zfmisc_1(X31,X32)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))),X34)
        | v1_partfun1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0)
        | k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))) = k2_relset_1(X31,X32,sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))) ) )).

tff(u3395,axiom,
    ( ~ ! [X11,X10,X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X10,X11),X12),X10,X11)
          | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),X12),X10)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X10,X11),X12))
          | k1_xboole_0 = X11
          | r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12)
          | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12 )
    | ! [X11,X10,X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X10,X11),X12),X10,X11)
        | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),X12),X10)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X10,X11),X12))
        | k1_xboole_0 = X11
        | r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12)
        | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12 ) )).

tff(u3394,axiom,
    ( ~ ! [X16,X17] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16,X17)
          | v1_partfun1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)))
          | k1_xboole_0 = X17
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)) )
    | ! [X16,X17] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16,X17)
        | v1_partfun1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)))
        | k1_xboole_0 = X17
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)) ) )).

tff(u3393,axiom,
    ( ~ ! [X18,X19] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18,X19)
          | v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)))
          | k1_xboole_0 = X19
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
          | v1_xboole_0(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X18,X19] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18,X19)
        | v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)))
        | k1_xboole_0 = X19
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
        | v1_xboole_0(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3392,axiom,
    ( ~ ! [X13,X15,X14] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13,X14)
          | v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)))
          | k1_xboole_0 = X14
          | r1_tarski(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X15)
          | k1_zfmisc_1(X15) = k1_zfmisc_1(k2_zfmisc_1(X13,X14)) )
    | ! [X13,X15,X14] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13,X14)
        | v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)))
        | k1_xboole_0 = X14
        | r1_tarski(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X15)
        | k1_zfmisc_1(X15) = k1_zfmisc_1(k2_zfmisc_1(X13,X14)) ) )).

tff(u3391,axiom,
    ( ~ ! [X16,X13,X15,X14] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15,X16)
          | k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | v1_partfun1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15)
          | k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
          | k1_xboole_0 = X16 )
    | ! [X16,X13,X15,X14] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15,X16)
        | k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | v1_partfun1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15)
        | k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))
        | k1_xboole_0 = X16 ) )).

tff(u3390,axiom,
    ( ~ ! [X9,X11,X10,X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,X12)
          | k2_relset_1(X9,X10,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
          | v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
          | k1_xboole_0 = X12 )
    | ! [X9,X11,X10,X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,X12)
        | k2_relset_1(X9,X10,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
        | v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
        | k1_xboole_0 = X12 ) )).

tff(u3389,axiom,
    ( ~ ! [X9,X11,X10,X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9,X10)
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
          | v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9)
          | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | k1_xboole_0 = X10 )
    | ! [X9,X11,X10,X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9,X10)
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))
        | v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9)
        | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | k1_xboole_0 = X10 ) )).

tff(u3388,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2)
          | k1_xboole_0 = X2
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
          | k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2)
        | k1_xboole_0 = X2
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
        | k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3387,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2)
          | k1_xboole_0 = X2
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
          | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2)
        | k1_xboole_0 = X2
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
        | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) ) )).

tff(u3386,axiom,
    ( ~ ! [X1,X3,X0,X2,X4] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)
          | k1_xboole_0 = X4
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )
    | ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)
        | k1_xboole_0 = X4
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) )).

tff(u3385,axiom,
    ( ~ ! [X1,X3,X0,X2,X4] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)
          | k1_xboole_0 = X4
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )
    | ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)
        | k1_xboole_0 = X4
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) )).

tff(u3384,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),X2),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2)))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2
          | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),X2),X0)
          | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),X2)) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),X2),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2)))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2
        | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),X2),X0)
        | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),X2)) ) )).

tff(u3383,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))))
          | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0)
          | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))
          | v1_partfun1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1)
          | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))))
        | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0)
        | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))
        | v1_partfun1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1)
        | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))) ) )).

tff(u3382,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X3,X0,X2] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3381,axiom,
    ( ~ ! [X13,X15,X12,X14] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14,X15)
          | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
          | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14)
          | k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
          | k1_xboole_0 = X15 )
    | ! [X13,X15,X12,X14] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14,X15)
        | k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
        | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14)
        | k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))
        | k1_xboole_0 = X15 ) )).

tff(u3380,axiom,
    ( ~ ! [X11,X13,X10,X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10,X11)
          | k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
          | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10)
          | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
          | k1_xboole_0 = X11 )
    | ! [X11,X13,X10,X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10,X11)
        | k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
        | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10)
        | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))
        | k1_xboole_0 = X11 ) )).

tff(u3379,axiom,
    ( ~ ! [X11,X13,X10,X12] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12,X13)
          | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
          | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12)
          | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))))
          | k1_xboole_0 = X13 )
    | ! [X11,X13,X10,X12] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12,X13)
        | k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))
        | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12)
        | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))))
        | k1_xboole_0 = X13 ) )).

tff(u3378,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
          | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )
    | ! [X1,X3,X0,X2] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
        | k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) )).

tff(u3377,axiom,
    ( ~ ! [X1,X3,X0,X2,X4] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X4)
          | k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X4)
          | k1_xboole_0 = X4
          | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X4)
        | k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X4)
        | k1_xboole_0 = X4
        | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3376,axiom,
    ( ~ ! [X1,X3,X0,X2,X4] :
          ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,X4)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)
          | k1_xboole_0 = X4
          | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
          | k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )
    | ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,X4)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)
        | k1_xboole_0 = X4
        | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
        | k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) )).

tff(u3375,axiom,
    ( ~ ! [X13] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0,X13)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))))
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0) )
    | ! [X13] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0,X13)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))))
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0) ) )).

tff(u3374,axiom,
    ( ~ ! [X12] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0,X12)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))))
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))))
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0) )
    | ! [X12] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0,X12)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))))
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))))
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0) ) )).

tff(u3373,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20)
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20)
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20)
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20)
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) ) )).

tff(u3372,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20)
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20)
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) ) )).

tff(u3371,axiom,
    ( ~ ! [X20,X21] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20,X21)
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))
          | k1_xboole_0 = X21
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X20,X21)) )
    | ! [X20,X21] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20,X21)
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))
        | k1_xboole_0 = X21
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X20,X21)) ) )).

tff(u3370,axiom,
    ( ~ ! [X22,X23] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22,X23)
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | k1_xboole_0 = X23
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X22,X23)) )
    | ! [X22,X23] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22,X23)
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | k1_xboole_0 = X23
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X22,X23)) ) )).

tff(u3369,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2)
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2)
          | k1_xboole_0 = X2
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2)
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2)
        | k1_xboole_0 = X2
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3368,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2)
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2)
          | k1_xboole_0 = X2
          | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2)
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2)
        | k1_xboole_0 = X2
        | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3367,axiom,
    ( ~ ! [X22,X23] :
          ( ~ v1_funct_2(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0,X23)
          | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23)) = k1_zfmisc_1(X22)
          | r1_tarski(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),X22)
          | ~ v1_funct_1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))))
          | v1_partfun1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0) )
    | ! [X22,X23] :
        ( ~ v1_funct_2(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0,X23)
        | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23)) = k1_zfmisc_1(X22)
        | r1_tarski(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),X22)
        | ~ v1_funct_1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))))
        | v1_partfun1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0) ) )).

tff(u3366,axiom,
    ( ~ ! [X20,X19] :
          ( ~ v1_funct_2(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,k2_relat_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))))
          | r1_tarski(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),X20)
          | v1_partfun1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
          | k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
          | ~ v1_funct_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) )
    | ! [X20,X19] :
        ( ~ v1_funct_2(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,k2_relat_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))))
        | r1_tarski(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),X20)
        | v1_partfun1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0)
        | k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))
        | ~ v1_funct_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) ) )).

tff(u3365,axiom,
    ( ~ ! [X25,X24,X26] :
          ( ~ v1_funct_2(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25,X26)
          | v1_partfun1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25)
          | ~ v1_funct_1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))
          | k1_xboole_0 = X26
          | r1_tarski(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X24)
          | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(X24) )
    | ! [X25,X24,X26] :
        ( ~ v1_funct_2(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25,X26)
        | v1_partfun1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25)
        | ~ v1_funct_1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))
        | k1_xboole_0 = X26
        | r1_tarski(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X24)
        | k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(X24) ) )).

tff(u3364,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ v1_funct_2(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
          | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)
          | k1_xboole_0 = k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | v1_partfun1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
          | ~ v1_funct_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
        | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)
        | k1_xboole_0 = k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | v1_partfun1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
        | ~ v1_funct_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3363,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(k2_zfmisc_1(X0,X1),X0,X1)
          | ~ v1_funct_1(k2_zfmisc_1(X0,X1))
          | ~ v1_partfun1(k2_zfmisc_1(X0,X1),X0) )
    | ! [X1,X0] :
        ( v1_funct_2(k2_zfmisc_1(X0,X1),X0,X1)
        | ~ v1_funct_1(k2_zfmisc_1(X0,X1))
        | ~ v1_partfun1(k2_zfmisc_1(X0,X1),X0) ) )).

tff(u3362,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(k2_zfmisc_1(X0,X1),X0,k2_relat_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(k2_zfmisc_1(X0,X1))
          | ~ v1_partfun1(k2_zfmisc_1(X0,X1),X0) )
    | ! [X1,X0] :
        ( v1_funct_2(k2_zfmisc_1(X0,X1),X0,k2_relat_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(k2_zfmisc_1(X0,X1))
        | ~ v1_partfun1(k2_zfmisc_1(X0,X1),X0) ) )).

tff(u3361,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

tff(u3360,negated_conjecture,
    ( ~ ! [X2] :
          ( v1_funct_2(sK2,k1_relat_1(sK2),X2)
          | ~ r1_tarski(k2_relat_1(sK2),X2) )
    | ! [X2] :
        ( v1_funct_2(sK2,k1_relat_1(sK2),X2)
        | ~ r1_tarski(k2_relat_1(sK2),X2) ) )).

tff(u3359,axiom,
    ( ~ ! [X5,X4] :
          ( v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
          | ~ v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4)
          | k1_xboole_0 = k2_zfmisc_1(X4,X5) )
    | ! [X5,X4] :
        ( v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
        | ~ v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4)
        | k1_xboole_0 = k2_zfmisc_1(X4,X5) ) )).

tff(u3358,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
          | ~ v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ! [X1,X0] :
        ( v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
        | ~ v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )).

tff(u3357,axiom,
    ( ~ ! [X5,X4] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5)
          | k1_xboole_0 = sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4) )
    | ! [X5,X4] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5)
        | k1_xboole_0 = sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4) ) )).

tff(u3356,axiom,
    ( ~ ! [X5,X4] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5)
          | v1_xboole_0(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4) )
    | ! [X5,X4] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5)
        | v1_xboole_0(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4) ) )).

tff(u3355,axiom,
    ( ~ ! [X22,X25,X23,X24] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24,X25)
          | k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))),sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
          | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24) )
    | ! [X22,X25,X23,X24] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24,X25)
        | k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))),sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))
        | k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24) ) )).

tff(u3354,axiom,
    ( ~ ! [X18,X20,X19,X21] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20,X21)
          | k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relat_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
          | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20) )
    | ! [X18,X20,X19,X21] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20,X21)
        | k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relat_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))
        | k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20) ) )).

tff(u3353,axiom,
    ( ~ ! [X5,X6] :
          ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5,X6)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
          | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5) )
    | ! [X5,X6] :
        ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5,X6)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5) ) )).

tff(u3352,axiom,
    ( ~ ! [X5,X4] :
          ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5)
          | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
          | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4) )
    | ! [X5,X4] :
        ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5)
        | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))
        | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4) ) )).

tff(u3351,axiom,
    ( ~ ! [X9,X7,X8] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8,k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7))))
          | r1_tarski(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X7)
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)))
          | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(X7) )
    | ! [X9,X7,X8] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8,k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7))))
        | r1_tarski(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X7)
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)))
        | k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(X7) ) )).

tff(u3350,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))))
          | k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) )
    | ! [X1,X0] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))))
        | k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u3349,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))))
          | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) )
    | ! [X1,X0] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))))
        | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u3348,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )
    | ! [X1,X3,X0,X2] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ) )).

tff(u3347,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )
    | ! [X1,X3,X0,X2] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ) )).

tff(u3346,axiom,
    ( ~ ! [X9,X11,X10,X12] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9)
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)) )
    | ! [X9,X11,X10,X12] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9)
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)) ) )).

tff(u3345,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
          | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ! [X1,X0] :
        ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
        | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) )).

tff(u3344,axiom,
    ( ~ ! [X1,X0] :
          ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
          | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
          | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
          | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )
    | ! [X1,X0] :
        ( v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)
        | ~ v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)
        | ~ v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
        | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) )).

tff(u3343,axiom,
    ( ~ ! [X9,X7,X8] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X7,X8),X9),X7,k2_relat_1(sK5(k2_zfmisc_1(X7,X8),X9)))
          | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X7,X8),X9),X7)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X7,X8),X9))
          | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9) )
    | ! [X9,X7,X8] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X7,X8),X9),X7,k2_relat_1(sK5(k2_zfmisc_1(X7,X8),X9)))
        | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X7,X8),X9),X7)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X7,X8),X9))
        | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9) ) )).

tff(u3342,axiom,
    ( ~ ! [X9,X7,X8] :
          ( v1_funct_2(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,k2_relat_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))
          | r1_tarski(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X9)
          | ~ v1_partfun1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
          | ~ v1_funct_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
          | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X9) )
    | ! [X9,X7,X8] :
        ( v1_funct_2(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,k2_relat_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))
        | r1_tarski(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X9)
        | ~ v1_partfun1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7)
        | ~ v1_funct_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))
        | k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X9) ) )).

tff(u3341,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )
    | ! [X1,X3,X0,X2] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) )).

tff(u3340,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
          | k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
          | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) )
    | ! [X1,X3,X0,X2] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))
        | k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
        | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)) ) )).

tff(u3339,axiom,
    ( ~ ! [X9,X11,X10,X12] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,k2_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))
          | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9)
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
          | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)) )
    | ! [X9,X11,X10,X12] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,k2_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))
        | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9)
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11)
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))
        | k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)) ) )).

tff(u3338,axiom,
    ( ~ ! [X22,X21,X23,X24] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23,X24)
          | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
          | k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) = k2_relset_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23) )
    | ! [X22,X21,X23,X24] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23,X24)
        | k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
        | k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) = k2_relset_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23) ) )).

tff(u3337,axiom,
    ( ~ ! [X20,X22,X19,X21] :
          ( v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19,X20)
          | k2_relset_1(X21,X22,sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) = k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))))
          | ~ v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))))
          | k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
          | ~ v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19) )
    | ! [X20,X22,X19,X21] :
        ( v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19,X20)
        | k2_relset_1(X21,X22,sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) = k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))))
        | ~ v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))))
        | k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))
        | ~ v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19) ) )).

tff(u3336,negated_conjecture,
    ( ~ ~ v2_struct_0(sK1)
    | ~ v2_struct_0(sK1) )).

tff(u3335,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u3334,axiom,
    ( ~ ! [X0] :
          ( ~ v2_struct_0(sK4(X0))
          | ~ l1_orders_2(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ v2_struct_0(sK4(X0))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) )).

tff(u3333,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | l1_struct_0(sK1) )).

tff(u3332,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u3331,axiom,
    ( ~ ! [X0] :
          ( l1_struct_0(sK4(X0))
          | ~ l1_orders_2(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( l1_struct_0(sK4(X0))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) )).

tff(u3330,axiom,
    ( ~ ! [X0] :
          ( ~ l1_orders_2(X0)
          | l1_struct_0(X0) )
    | ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) )).

tff(u3329,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u3328,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u3327,axiom,
    ( ~ ! [X0] :
          ( l1_orders_2(sK4(X0))
          | v2_struct_0(X0)
          | ~ l1_orders_2(X0) )
    | ! [X0] :
        ( l1_orders_2(sK4(X0))
        | v2_struct_0(X0)
        | ~ l1_orders_2(X0) ) )).

tff(u3326,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_yellow_0(X1,X0)
          | u1_orders_2(X1) = u1_orders_2(X0)
          | ~ m1_yellow_0(X0,X1)
          | ~ l1_orders_2(X1) )
    | ! [X1,X0] :
        ( ~ m1_yellow_0(X1,X0)
        | u1_orders_2(X1) = u1_orders_2(X0)
        | ~ m1_yellow_0(X0,X1)
        | ~ l1_orders_2(X1) ) )).

tff(u3325,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_yellow_0(X1,X0)
          | u1_struct_0(X0) = u1_struct_0(X1)
          | ~ m1_yellow_0(X0,X1)
          | ~ l1_orders_2(X1) )
    | ! [X1,X0] :
        ( ~ m1_yellow_0(X1,X0)
        | u1_struct_0(X0) = u1_struct_0(X1)
        | ~ m1_yellow_0(X0,X1)
        | ~ l1_orders_2(X1) ) )).

tff(u3324,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_yellow_0(X1,X0)
          | l1_orders_2(X1)
          | ~ l1_orders_2(X0) )
    | ! [X1,X0] :
        ( ~ m1_yellow_0(X1,X0)
        | l1_orders_2(X1)
        | ~ l1_orders_2(X0) ) )).

tff(u3323,axiom,
    ( ~ ! [X0] :
          ( ~ m1_yellow_0(X0,sK4(X0))
          | u1_orders_2(X0) = u1_orders_2(sK4(X0))
          | ~ l1_orders_2(sK4(X0))
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ m1_yellow_0(X0,sK4(X0))
        | u1_orders_2(X0) = u1_orders_2(sK4(X0))
        | ~ l1_orders_2(sK4(X0))
        | v2_struct_0(X0) ) )).

tff(u3322,axiom,
    ( ~ ! [X0] :
          ( ~ m1_yellow_0(X0,sK4(X0))
          | u1_struct_0(X0) = u1_struct_0(sK4(X0))
          | ~ l1_orders_2(sK4(X0))
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ m1_yellow_0(X0,sK4(X0))
        | u1_struct_0(X0) = u1_struct_0(sK4(X0))
        | ~ l1_orders_2(sK4(X0))
        | v2_struct_0(X0) ) )).

tff(u3321,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_yellow_0(sK0,X0)
          | ~ m1_yellow_0(X0,sK0)
          | u1_struct_0(X0) = k1_relat_1(sK2)
          | ~ l1_orders_2(X0) )
    | ! [X0] :
        ( ~ m1_yellow_0(sK0,X0)
        | ~ m1_yellow_0(X0,sK0)
        | u1_struct_0(X0) = k1_relat_1(sK2)
        | ~ l1_orders_2(X0) ) )).

tff(u3320,axiom,
    ( ~ ! [X0] :
          ( m1_yellow_0(sK4(X0),X0)
          | ~ l1_orders_2(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( m1_yellow_0(sK4(X0),X0)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) )).

tff(u3319,axiom,
    ( ~ ! [X2] :
          ( m1_yellow_0(X2,X2)
          | ~ l1_orders_2(X2) )
    | ! [X2] :
        ( m1_yellow_0(X2,X2)
        | ~ l1_orders_2(X2) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 15:01:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.51  % (17489)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (17486)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (17513)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (17492)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (17497)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (17500)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (17495)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (17511)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (17488)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (17513)Refutation not found, incomplete strategy% (17513)------------------------------
% 0.22/0.54  % (17513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17487)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (17513)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17513)Memory used [KB]: 6268
% 0.22/0.54  % (17513)Time elapsed: 0.126 s
% 0.22/0.54  % (17513)------------------------------
% 0.22/0.54  % (17513)------------------------------
% 0.22/0.54  % (17487)Refutation not found, incomplete strategy% (17487)------------------------------
% 0.22/0.54  % (17487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17487)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17487)Memory used [KB]: 1663
% 0.22/0.54  % (17487)Time elapsed: 0.124 s
% 0.22/0.54  % (17487)------------------------------
% 0.22/0.54  % (17487)------------------------------
% 0.22/0.55  % (17501)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (17509)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (17507)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (17493)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (17494)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (17490)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (17496)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (17512)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (17511)Refutation not found, incomplete strategy% (17511)------------------------------
% 0.22/0.56  % (17511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17511)Memory used [KB]: 6396
% 0.22/0.56  % (17511)Time elapsed: 0.143 s
% 0.22/0.56  % (17511)------------------------------
% 0.22/0.56  % (17511)------------------------------
% 0.22/0.56  % (17510)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (17502)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (17515)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (17515)Refutation not found, incomplete strategy% (17515)------------------------------
% 0.22/0.56  % (17515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17515)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17515)Memory used [KB]: 1663
% 0.22/0.56  % (17515)Time elapsed: 0.129 s
% 0.22/0.56  % (17515)------------------------------
% 0.22/0.56  % (17515)------------------------------
% 1.53/0.56  % (17512)Refutation not found, incomplete strategy% (17512)------------------------------
% 1.53/0.56  % (17512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (17512)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (17512)Memory used [KB]: 6396
% 1.53/0.56  % (17512)Time elapsed: 0.149 s
% 1.53/0.56  % (17512)------------------------------
% 1.53/0.56  % (17512)------------------------------
% 1.53/0.56  % (17499)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.53/0.57  % (17514)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.53/0.57  % (17502)Refutation not found, incomplete strategy% (17502)------------------------------
% 1.53/0.57  % (17502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (17502)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (17502)Memory used [KB]: 10746
% 1.53/0.57  % (17502)Time elapsed: 0.156 s
% 1.53/0.57  % (17502)------------------------------
% 1.53/0.57  % (17502)------------------------------
% 1.53/0.57  % (17506)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.57  % (17504)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.53/0.58  % (17503)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.58  % (17491)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.53/0.58  % (17498)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.58  % (17496)Refutation not found, incomplete strategy% (17496)------------------------------
% 1.53/0.58  % (17496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (17496)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (17496)Memory used [KB]: 10746
% 1.53/0.58  % (17496)Time elapsed: 0.167 s
% 1.53/0.58  % (17496)------------------------------
% 1.53/0.58  % (17496)------------------------------
% 1.53/0.58  % (17503)Refutation not found, incomplete strategy% (17503)------------------------------
% 1.53/0.58  % (17503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (17503)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (17503)Memory used [KB]: 1791
% 1.53/0.58  % (17503)Time elapsed: 0.155 s
% 1.53/0.58  % (17503)------------------------------
% 1.53/0.58  % (17503)------------------------------
% 1.53/0.58  % (17504)Refutation not found, incomplete strategy% (17504)------------------------------
% 1.53/0.58  % (17504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (17504)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (17504)Memory used [KB]: 1791
% 1.53/0.58  % (17504)Time elapsed: 0.169 s
% 1.53/0.58  % (17504)------------------------------
% 1.53/0.58  % (17504)------------------------------
% 1.66/0.59  % (17514)Refutation not found, incomplete strategy% (17514)------------------------------
% 1.66/0.59  % (17514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (17514)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (17514)Memory used [KB]: 10874
% 1.66/0.59  % (17514)Time elapsed: 0.179 s
% 1.66/0.59  % (17514)------------------------------
% 1.66/0.59  % (17514)------------------------------
% 1.66/0.59  % (17505)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.59  % (17498)Refutation not found, incomplete strategy% (17498)------------------------------
% 1.66/0.59  % (17498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (17498)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (17498)Memory used [KB]: 10746
% 1.66/0.59  % (17498)Time elapsed: 0.170 s
% 1.66/0.59  % (17498)------------------------------
% 1.66/0.59  % (17498)------------------------------
% 1.66/0.61  % (17508)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.66/0.63  % (17489)Refutation not found, incomplete strategy% (17489)------------------------------
% 1.66/0.63  % (17489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (17489)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (17489)Memory used [KB]: 6140
% 1.66/0.63  % (17489)Time elapsed: 0.212 s
% 1.66/0.63  % (17489)------------------------------
% 1.66/0.63  % (17489)------------------------------
% 2.13/0.67  % (17517)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.13/0.68  % (17520)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.13/0.69  % (17524)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.13/0.69  % (17525)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.13/0.69  % (17520)Refutation not found, incomplete strategy% (17520)------------------------------
% 2.13/0.69  % (17520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.69  % (17518)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.13/0.70  % (17516)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.13/0.70  % (17520)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.70  
% 2.13/0.70  % (17520)Memory used [KB]: 10746
% 2.13/0.70  % (17520)Time elapsed: 0.092 s
% 2.13/0.70  % (17520)------------------------------
% 2.13/0.70  % (17520)------------------------------
% 2.13/0.71  % (17521)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.51/0.71  % (17519)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.51/0.72  % (17518)Refutation not found, incomplete strategy% (17518)------------------------------
% 2.51/0.72  % (17518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.72  % (17518)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.72  
% 2.51/0.72  % (17518)Memory used [KB]: 6140
% 2.51/0.72  % (17518)Time elapsed: 0.122 s
% 2.51/0.72  % (17518)------------------------------
% 2.51/0.72  % (17518)------------------------------
% 2.51/0.75  % (17526)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.78/0.77  % (17526)Refutation not found, incomplete strategy% (17526)------------------------------
% 2.78/0.77  % (17526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.77  % (17526)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.77  
% 2.78/0.77  % (17526)Memory used [KB]: 10874
% 2.78/0.77  % (17526)Time elapsed: 0.138 s
% 2.78/0.77  % (17526)------------------------------
% 2.78/0.77  % (17526)------------------------------
% 2.78/0.77  % (17527)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.78/0.79  % (17528)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.78/0.80  % (17523)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.78/0.81  % (17501)Refutation not found, incomplete strategy% (17501)------------------------------
% 2.78/0.81  % (17501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.82  % (17510)Time limit reached!
% 2.78/0.82  % (17510)------------------------------
% 2.78/0.82  % (17510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.82  % (17510)Termination reason: Time limit
% 2.78/0.82  
% 2.78/0.82  % (17510)Memory used [KB]: 13176
% 2.78/0.82  % (17510)Time elapsed: 0.403 s
% 2.78/0.82  % (17510)------------------------------
% 2.78/0.82  % (17510)------------------------------
% 2.78/0.82  % (17488)Time limit reached!
% 2.78/0.82  % (17488)------------------------------
% 2.78/0.82  % (17488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.82  % (17488)Termination reason: Time limit
% 2.78/0.82  
% 2.78/0.82  % (17488)Memory used [KB]: 6652
% 2.78/0.82  % (17488)Time elapsed: 0.403 s
% 2.78/0.82  % (17488)------------------------------
% 2.78/0.82  % (17488)------------------------------
% 2.78/0.82  % (17501)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.83  
% 2.78/0.83  % (17501)Memory used [KB]: 6268
% 2.78/0.83  % (17501)Time elapsed: 0.377 s
% 2.78/0.83  % (17501)------------------------------
% 2.78/0.83  % (17501)------------------------------
% 2.78/0.83  % (17529)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.78/0.84  % (17530)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.46/0.93  % (17531)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.46/0.93  % (17492)Time limit reached!
% 3.46/0.93  % (17492)------------------------------
% 3.46/0.93  % (17492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.93  % (17492)Termination reason: Time limit
% 3.46/0.93  
% 3.46/0.93  % (17492)Memory used [KB]: 13560
% 3.46/0.93  % (17492)Time elapsed: 0.506 s
% 3.46/0.93  % (17492)------------------------------
% 3.46/0.93  % (17492)------------------------------
% 3.46/0.93  % (17500)Time limit reached!
% 3.46/0.93  % (17500)------------------------------
% 3.46/0.93  % (17500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.93  % (17500)Termination reason: Time limit
% 3.46/0.93  % (17500)Termination phase: Saturation
% 3.46/0.93  
% 3.46/0.93  % (17500)Memory used [KB]: 4221
% 3.46/0.93  % (17500)Time elapsed: 0.500 s
% 3.46/0.93  % (17500)------------------------------
% 3.46/0.93  % (17500)------------------------------
% 3.80/0.96  % (17533)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.80/0.96  % (17534)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.80/0.99  % (17532)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 4.05/1.03  % (17493)Time limit reached!
% 4.05/1.03  % (17493)------------------------------
% 4.05/1.03  % (17493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/1.03  % (17493)Termination reason: Time limit
% 4.05/1.03  
% 4.05/1.03  % (17493)Memory used [KB]: 4989
% 4.05/1.03  % (17493)Time elapsed: 0.608 s
% 4.05/1.03  % (17493)------------------------------
% 4.05/1.03  % (17493)------------------------------
% 5.55/1.07  % (17525)Refutation not found, incomplete strategy% (17525)------------------------------
% 5.55/1.07  % (17525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.55/1.07  % (17525)Termination reason: Refutation not found, incomplete strategy
% 5.55/1.07  
% 5.55/1.07  % (17525)Memory used [KB]: 6780
% 5.55/1.07  % (17525)Time elapsed: 0.433 s
% 5.55/1.07  % (17525)------------------------------
% 5.55/1.07  % (17525)------------------------------
% 5.55/1.08  % (17536)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 5.55/1.08  % (17535)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 5.55/1.10  % SZS status CounterSatisfiable for theBenchmark
% 5.55/1.11  % (17533)# SZS output start Saturation.
% 5.55/1.11  tff(u3663,axiom,
% 5.55/1.11      ((~(![X1, X0] : (((k1_xboole_0 != X0) | ~r2_hidden(X1,k1_zfmisc_1(X0)) | (k1_xboole_0 = X1))))) | (![X1, X0] : (((k1_xboole_0 != X0) | ~r2_hidden(X1,k1_zfmisc_1(X0)) | (k1_xboole_0 = X1)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3662,axiom,
% 5.55/1.11      ((~(![X0, X2] : (((k1_xboole_0 != k3_tarski(X0)) | ~r2_hidden(X2,X0) | (k1_xboole_0 = X2))))) | (![X0, X2] : (((k1_xboole_0 != k3_tarski(X0)) | ~r2_hidden(X2,X0) | (k1_xboole_0 = X2)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3661,negated_conjecture,
% 5.55/1.11      ((~(k1_xboole_0 != k2_relat_1(sK2))) | (k1_xboole_0 != k2_relat_1(sK2)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3660,negated_conjecture,
% 5.55/1.11      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (k1_xboole_0 != u1_struct_0(sK1)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3659,axiom,
% 5.55/1.11      ((~(![X0] : (((k1_xboole_0 != sK3(X0)) | (k1_xboole_0 = k3_tarski(X0)))))) | (![X0] : (((k1_xboole_0 != sK3(X0)) | (k1_xboole_0 = k3_tarski(X0))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3658,negated_conjecture,
% 5.55/1.11      ((~(k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2))) | (k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3657,negated_conjecture,
% 5.55/1.11      ((~(k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2))) | (k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3656,negated_conjecture,
% 5.55/1.11      ((~(sK2 != k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (sK2 != k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3655,negated_conjecture,
% 5.55/1.11      ((~(sK2 != k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (sK2 != k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3654,axiom,
% 5.55/1.11      ((~(![X0] : ((k1_xboole_0 = k1_subset_1(X0))))) | (![X0] : ((k1_xboole_0 = k1_subset_1(X0)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3653,axiom,
% 5.55/1.11      ((~(![X0] : ((k3_tarski(k1_zfmisc_1(X0)) = X0)))) | (![X0] : ((k3_tarski(k1_zfmisc_1(X0)) = X0))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3652,axiom,
% 5.55/1.11      ((~(![X1, X0] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = k2_relset_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))))) | (![X1, X0] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = k2_relset_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3651,negated_conjecture,
% 5.55/1.11      ((~(k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3650,axiom,
% 5.55/1.11      ((~(![X1, X0] : (((k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | (k1_xboole_0 = k2_zfmisc_1(X0,X1)))))) | (![X1, X0] : (((k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | (k1_xboole_0 = k2_zfmisc_1(X0,X1))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3649,axiom,
% 5.55/1.11      ((~(![X3, X4] : (((k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X3,k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))))))) | (![X3, X4] : (((k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X3,k2_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3648,axiom,
% 5.55/1.11      ((~(![X16, X15, X17, X14] : (((k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X14,k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))))) | (![X16, X15, X17, X14] : (((k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X14,k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3647,axiom,
% 5.55/1.11      ((~(![X1, X0, X2] : (((k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2))))))) | (![X1, X0, X2] : (((k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3646,axiom,
% 5.55/1.11      ((~(![X9, X10] : (((k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relset_1(X9,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))))) | (![X9, X10] : (((k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relset_1(X9,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3645,axiom,
% 5.55/1.11      ((~(![X3, X5, X2, X4] : (((k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X4,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (![X3, X5, X2, X4] : (((k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X4,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3644,axiom,
% 5.55/1.11      ((~(![X27, X29, X26, X28] : (((k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X26,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27))))) | (k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29))) | (k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X28,X29,sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))))) | (![X27, X29, X26, X28] : (((k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X26,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27))))) | (k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29))) | (k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))) = k2_relset_1(X28,X29,sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3643,negated_conjecture,
% 5.55/1.11      ((~(k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2))) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3642,axiom,
% 5.55/1.11      ((~(![X1, X0] : ((k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0))))) | (![X1, X0] : ((k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3641,axiom,
% 5.55/1.11      ((~(![X1, X0] : ((k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k2_relat_1(k2_zfmisc_1(X0,X1)))))) | (![X1, X0] : ((k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k2_relat_1(k2_zfmisc_1(X0,X1))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3640,axiom,
% 5.55/1.11      ((~(![X5, X4] : (((k2_relset_1(X4,X5,sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))))) | (k1_xboole_0 = k2_zfmisc_1(X4,X5)))))) | (![X5, X4] : (((k2_relset_1(X4,X5,sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))))) | (k1_xboole_0 = k2_zfmisc_1(X4,X5))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3639,axiom,
% 5.55/1.11      ((~(![X7, X6] : (((k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))) | (![X7, X6] : (((k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3638,axiom,
% 5.55/1.11      ((~(![X22, X25, X23, X24] : (((k2_relset_1(X24,X25,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))) | (k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))) | (![X22, X25, X23, X24] : (((k2_relset_1(X24,X25,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))) | (k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3637,axiom,
% 5.55/1.11      ((~(![X7, X8] : (((k2_relset_1(X7,X8,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))))) | (![X7, X8] : (((k2_relset_1(X7,X8,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3636,negated_conjecture,
% 5.55/1.11      ((~(u1_struct_0(sK0) = k1_relat_1(sK2))) | (u1_struct_0(sK0) = k1_relat_1(sK2)))).
% 5.55/1.11  
% 5.55/1.11  tff(u3635,axiom,
% 5.55/1.11      ((~(![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))) | (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3634,axiom,
% 5.55/1.11      ((~(![X1] : ((~r1_tarski(X1,k1_xboole_0) | (k1_xboole_0 = X1))))) | (![X1] : ((~r1_tarski(X1,k1_xboole_0) | (k1_xboole_0 = X1)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3633,axiom,
% 5.55/1.11      ((~(![X0] : ((~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0))))) | (![X0] : ((~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3632,axiom,
% 5.55/1.11      ((~(![X1, X0, X2] : ((~r1_tarski(X1,k2_zfmisc_1(X2,X0)) | v1_partfun1(X1,X2) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | (k1_xboole_0 = X0))))) | (![X1, X0, X2] : ((~r1_tarski(X1,k2_zfmisc_1(X2,X0)) | v1_partfun1(X1,X2) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | (k1_xboole_0 = X0)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3631,axiom,
% 5.55/1.11      ((~(![X3, X5, X2, X4] : ((~r1_tarski(X2,k2_zfmisc_1(X4,X5)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~r1_tarski(k2_relat_1(X2),X3))))) | (![X3, X5, X2, X4] : ((~r1_tarski(X2,k2_zfmisc_1(X4,X5)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~r1_tarski(k2_relat_1(X2),X3)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3630,axiom,
% 5.55/1.11      ((~(![X3, X2, X4] : ((~r1_tarski(X2,k2_zfmisc_1(X3,X4)) | ~v1_funct_1(X2) | v1_funct_2(X2,X3,X4) | ~v1_partfun1(X2,X3))))) | (![X3, X2, X4] : ((~r1_tarski(X2,k2_zfmisc_1(X3,X4)) | ~v1_funct_1(X2) | v1_funct_2(X2,X3,X4) | ~v1_partfun1(X2,X3)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3629,axiom,
% 5.55/1.11      ((~(![X3, X2, X4] : ((~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | (k2_relset_1(X2,X3,X4) = k2_relat_1(X4)))))) | (![X3, X2, X4] : ((~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | (k2_relset_1(X2,X3,X4) = k2_relat_1(X4))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3628,axiom,
% 5.55/1.11      ((~(![X1, X3, X2] : ((~r1_tarski(X1,k2_zfmisc_1(X2,X3)) | v4_relat_1(X1,X2))))) | (![X1, X3, X2] : ((~r1_tarski(X1,k2_zfmisc_1(X2,X3)) | v4_relat_1(X1,X2)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3627,axiom,
% 5.55/1.11      ((~(![X1, X0, X2] : ((~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0))))) | (![X1, X0, X2] : ((~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3626,axiom,
% 5.55/1.11      ((~(![X1, X2] : ((~r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2)) | ~v1_funct_2(X1,k1_xboole_0,X2) | ~v1_funct_1(X1) | v1_partfun1(X1,k1_xboole_0))))) | (![X1, X2] : ((~r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2)) | ~v1_funct_2(X1,k1_xboole_0,X2) | ~v1_funct_1(X1) | v1_partfun1(X1,k1_xboole_0)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3625,axiom,
% 5.55/1.11      ((~(![X2] : ((~r1_tarski(X2,sK3(k1_zfmisc_1(X2))) | (sK3(k1_zfmisc_1(X2)) = X2) | (k1_xboole_0 = X2))))) | (![X2] : ((~r1_tarski(X2,sK3(k1_zfmisc_1(X2))) | (sK3(k1_zfmisc_1(X2)) = X2) | (k1_xboole_0 = X2)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3624,axiom,
% 5.55/1.11      ((~(![X1, X0] : ((~r1_tarski(X0,sK5(X0,X1)) | (k1_zfmisc_1(X0) = X1) | (sK5(X0,X1) = X0) | r2_hidden(sK5(X0,X1),X1))))) | (![X1, X0] : ((~r1_tarski(X0,sK5(X0,X1)) | (k1_zfmisc_1(X0) = X1) | (sK5(X0,X1) = X0) | r2_hidden(sK5(X0,X1),X1)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3623,axiom,
% 5.55/1.11      ((~(![X0] : ((~r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = sK5(X0,k1_zfmisc_1(k1_xboole_0))) | (sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)))))) | (![X0] : ((~r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = sK5(X0,k1_zfmisc_1(k1_xboole_0))) | (sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3622,axiom,
% 5.55/1.11      ((~(![X0] : ((~r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0))) | v1_xboole_0(sK5(X0,k1_zfmisc_1(k1_xboole_0))) | (sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)))))) | (![X0] : ((~r1_tarski(X0,sK5(X0,k1_zfmisc_1(k1_xboole_0))) | v1_xboole_0(sK5(X0,k1_zfmisc_1(k1_xboole_0))) | (sK5(X0,k1_zfmisc_1(k1_xboole_0)) = X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3621,axiom,
% 5.55/1.11      ((~(![X1, X2] : ((~r1_tarski(X1,sK5(X1,k1_zfmisc_1(X2))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(X2)) | (sK5(X1,k1_zfmisc_1(X2)) = X1) | r1_tarski(sK5(X1,k1_zfmisc_1(X2)),X2))))) | (![X1, X2] : ((~r1_tarski(X1,sK5(X1,k1_zfmisc_1(X2))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(X2)) | (sK5(X1,k1_zfmisc_1(X2)) = X1) | r1_tarski(sK5(X1,k1_zfmisc_1(X2)),X2)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3620,axiom,
% 5.55/1.11      ((~(![X7, X8, X6] : ((~r1_tarski(X8,sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | (k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X6,k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))),sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))) | (sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) = X8) | (k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = k1_zfmisc_1(X8)))))) | (![X7, X8, X6] : ((~r1_tarski(X8,sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | (k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relset_1(X6,k2_relat_1(sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))),sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))) | (sK5(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) = X8) | (k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = k1_zfmisc_1(X8))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3619,axiom,
% 5.55/1.11      ((~(![X3, X2, X4] : ((~r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k2_relset_1(X2,X3,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4) | (k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (![X3, X2, X4] : ((~r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k2_relset_1(X2,X3,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4) | (k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3618,axiom,
% 5.55/1.11      ((~(![X3, X2, X4] : ((~r1_tarski(X2,sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | (sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = X2) | v4_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3))))) | (![X3, X2, X4] : ((~r1_tarski(X2,sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | (sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) = X2) | v4_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3617,axiom,
% 5.55/1.11      ((~(![X3, X2, X4] : ((~r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | v1_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4) | (k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (![X3, X2, X4] : ((~r1_tarski(X4,sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | v1_relat_1(sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (sK5(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = X4) | (k1_zfmisc_1(X4) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3616,axiom,
% 5.55/1.11      ((~(![X3, X2] : ((~r1_tarski(X3,sK5(X2,k1_zfmisc_1(X3))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(X3)) | (sK5(X2,k1_zfmisc_1(X3)) = X3) | r1_tarski(sK5(X2,k1_zfmisc_1(X3)),X2))))) | (![X3, X2] : ((~r1_tarski(X3,sK5(X2,k1_zfmisc_1(X3))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(X3)) | (sK5(X2,k1_zfmisc_1(X3)) = X3) | r1_tarski(sK5(X2,k1_zfmisc_1(X3)),X2)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3615,axiom,
% 5.55/1.11      ((~(![X1] : ((~r1_tarski(X1,sK5(k1_xboole_0,k1_zfmisc_1(X1))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)) | (sK5(k1_xboole_0,k1_zfmisc_1(X1)) = X1) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X1))))))) | (![X1] : ((~r1_tarski(X1,sK5(k1_xboole_0,k1_zfmisc_1(X1))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)) | (sK5(k1_xboole_0,k1_zfmisc_1(X1)) = X1) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X1)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3614,axiom,
% 5.55/1.11      ((~(![X0] : ((~r1_tarski(X0,sK5(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)) | (sK5(k1_xboole_0,k1_zfmisc_1(X0)) = X0) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0))))))) | (![X0] : ((~r1_tarski(X0,sK5(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)) | (sK5(k1_xboole_0,k1_zfmisc_1(X0)) = X0) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3613,axiom,
% 5.55/1.11      ((~(![X5, X7, X6] : ((~r1_tarski(X7,sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) | (k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | (sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)) = X7) | (k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)))))))) | (![X5, X7, X6] : ((~r1_tarski(X7,sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) | (k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | (sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)) = X7) | (k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3612,axiom,
% 5.55/1.11      ((~(![X3, X5, X4] : ((~r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) | (k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))) | (sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3)))))) | (![X3, X5, X4] : ((~r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) | (k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)))) | (sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3611,axiom,
% 5.55/1.11      ((~(![X3, X5, X4] : ((~r1_tarski(X5,sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5))) | (k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(X5)) | (sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)) = X5) | v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)),X3))))) | (![X3, X5, X4] : ((~r1_tarski(X5,sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5))) | (k1_zfmisc_1(k2_zfmisc_1(X3,X4)) = k1_zfmisc_1(X5)) | (sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)) = X5) | v4_relat_1(sK5(k2_zfmisc_1(X3,X4),k1_zfmisc_1(X5)),X3)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3610,axiom,
% 5.55/1.11      ((~(![X3, X5, X4] : ((~r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) | v1_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) | (sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3)))))) | (![X3, X5, X4] : ((~r1_tarski(X3,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) | v1_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3))) | (sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(X3)) = X3) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(X3))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3609,negated_conjecture,
% 5.55/1.11      ((~(![X3] : ((~r1_tarski(k2_relat_1(sK2),X3) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),X3,sK2)))))) | (![X3] : ((~r1_tarski(k2_relat_1(sK2),X3) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),X3,sK2))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3608,axiom,
% 5.55/1.11      ((~(![X1, X0] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) | (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1)))),X1) | (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,k2_relat_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3607,axiom,
% 5.55/1.11      ((~(![X1, X0, X2] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),X1) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2))))))) | (![X1, X0, X2] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),X1) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3606,axiom,
% 5.55/1.11      ((~(![X5, X4, X6] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X4,X5)),X6) | ~v1_partfun1(k2_zfmisc_1(X4,X5),X4) | ~v1_funct_1(k2_zfmisc_1(X4,X5)) | v1_funct_2(k2_zfmisc_1(X4,X5),X4,X6))))) | (![X5, X4, X6] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X4,X5)),X6) | ~v1_partfun1(k2_zfmisc_1(X4,X5),X4) | ~v1_funct_1(k2_zfmisc_1(X4,X5)) | v1_funct_2(k2_zfmisc_1(X4,X5),X4,X6)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3605,axiom,
% 5.55/1.11      ((~(![X1, X0, X2] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X2)),X1) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X2) | (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,X2)))))) | (![X1, X0, X2] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X2)),X1) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X2) | (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X0,X2))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3604,axiom,
% 5.55/1.11      ((~(![X9, X7, X8] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X7,X8)),X9) | (k2_relat_1(k2_zfmisc_1(X7,X8)) = k2_relset_1(X7,X9,k2_zfmisc_1(X7,X8))))))) | (![X9, X7, X8] : ((~r1_tarski(k2_relat_1(k2_zfmisc_1(X7,X8)),X9) | (k2_relat_1(k2_zfmisc_1(X7,X8)) = k2_relset_1(X7,X9,k2_zfmisc_1(X7,X8)))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3603,axiom,
% 5.55/1.11      ((~(![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | (k1_xboole_0 = k2_zfmisc_1(X7,X8)) | ~v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9))))) | (![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | (k1_xboole_0 = k2_zfmisc_1(X7,X8)) | ~v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3602,axiom,
% 5.55/1.11      ((~(![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12) | (k1_xboole_0 = k2_zfmisc_1(X10,X11)) | (k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))))) | (![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12) | (k1_xboole_0 = k2_zfmisc_1(X10,X11)) | (k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK3(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3601,axiom,
% 5.55/1.11      ((~(![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9))))) | (![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3600,axiom,
% 5.55/1.11      ((~(![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v1_xboole_0(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9))))) | (![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))),X9) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v1_xboole_0(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0))) | v1_funct_2(sK5(k2_zfmisc_1(X7,X8),k1_zfmisc_1(k1_xboole_0)),X7,X9)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3599,axiom,
% 5.55/1.11      ((~(![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))))))) | (![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3598,axiom,
% 5.55/1.11      ((~(![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0)))))))) | (![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))),X12) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k2_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X10,X12,sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3597,axiom,
% 5.55/1.11      ((~(![X5, X4, X6] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))),X6) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X4,X6))) | (k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))) = k2_relset_1(X4,X6,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6))))))))) | (![X5, X4, X6] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))),X6) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = k1_zfmisc_1(k2_zfmisc_1(X4,X6))) | (k2_relat_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))) = k2_relset_1(X4,X6,sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X6)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3596,axiom,
% 5.55/1.11      ((~(![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9))))) | (![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3595,axiom,
% 5.55/1.11      ((~(![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9))))) | (![X9, X7, X8] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,X9)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3594,axiom,
% 5.55/1.11      ((~(![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | (k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))))) | (![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | (k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3593,axiom,
% 5.55/1.11      ((~(![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | (k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))))) | (![X11, X10, X12] : ((~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),X12) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | (k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,X12,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3592,axiom,
% 5.55/1.11      ((~(![X11, X13, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),X13)),X14) | m1_subset_1(sK5(k2_zfmisc_1(X11,X12),X13),k1_zfmisc_1(k2_zfmisc_1(X11,X14))) | r2_hidden(sK5(k2_zfmisc_1(X11,X12),X13),X13) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = X13))))) | (![X11, X13, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),X13)),X14) | m1_subset_1(sK5(k2_zfmisc_1(X11,X12),X13),k1_zfmisc_1(k2_zfmisc_1(X11,X14))) | r2_hidden(sK5(k2_zfmisc_1(X11,X12),X13),X13) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = X13)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3591,axiom,
% 5.55/1.11      ((~(![X5, X7, X8, X6] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),X8) | (k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | m1_subset_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),k1_zfmisc_1(k2_zfmisc_1(X5,X8))) | r1_tarski(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),X7))))) | (![X5, X7, X8, X6] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7))),X8) | (k1_zfmisc_1(X7) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | m1_subset_1(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),k1_zfmisc_1(k2_zfmisc_1(X5,X8))) | r1_tarski(sK5(k2_zfmisc_1(X5,X6),k1_zfmisc_1(X7)),X7)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3590,axiom,
% 5.55/1.11      ((~(![X9, X7, X8, X6] : ((~r1_tarski(k2_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X6)) | m1_subset_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),k1_zfmisc_1(k2_zfmisc_1(X7,X9))) | r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6))))) | (![X9, X7, X8, X6] : ((~r1_tarski(k2_relat_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))),X9) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X6)) | m1_subset_1(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),k1_zfmisc_1(k2_zfmisc_1(X7,X9))) | r1_tarski(sK5(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X6)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3589,axiom,
% 5.55/1.11      ((~(![X16, X13, X15, X17, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16)))),X17) | (k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | m1_subset_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),k1_zfmisc_1(k2_zfmisc_1(X13,X17))) | v4_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),X15))))) | (![X16, X13, X15, X17, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16)))),X17) | (k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | m1_subset_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),k1_zfmisc_1(k2_zfmisc_1(X13,X17))) | v4_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X15,X16))),X15)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3588,axiom,
% 5.55/1.11      ((~(![X16, X18, X15, X17, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X18) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | m1_subset_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),k1_zfmisc_1(k2_zfmisc_1(X16,X18))) | v4_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),X14))))) | (![X16, X18, X15, X17, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X18) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | m1_subset_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),k1_zfmisc_1(k2_zfmisc_1(X16,X18))) | v4_relat_1(sK5(k2_zfmisc_1(X14,X15),k1_zfmisc_1(k2_zfmisc_1(X16,X17))),X14)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3587,axiom,
% 5.55/1.11      ((~(![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | (k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15))))) | (![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | (k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3586,axiom,
% 5.55/1.11      ((~(![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))))) | (![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3585,axiom,
% 5.55/1.11      ((~(![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | (k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X11,X12,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13,X15))))) | (![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | (k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X11,X12,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X13,X15)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3584,axiom,
% 5.55/1.11      ((~(![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))))) | (![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3583,axiom,
% 5.55/1.11      ((~(![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | (k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15))))) | (![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | (k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X11,X15)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3582,axiom,
% 5.55/1.11      ((~(![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))))) | (![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3581,axiom,
% 5.55/1.11      ((~(![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),X15) | (k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X15))))) | (![X11, X13, X15, X12, X14] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),X15) | (k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X15)))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3580,axiom,
% 5.55/1.11      ((~(![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X20) | (k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))))) | (![X16, X18, X20, X17, X19] : ((~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),X20) | (k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17))))) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) = k2_relset_1(X16,X20,sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3579,negated_conjecture,
% 5.55/1.11      ((~~r1_tarski(k2_relat_1(sK2),k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0))).
% 5.55/1.11  
% 5.55/1.11  tff(u3578,negated_conjecture,
% 5.55/1.11      ((~~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3577,negated_conjecture,
% 5.55/1.11      ((~~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))).
% 5.55/1.11  
% 5.55/1.11  tff(u3576,negated_conjecture,
% 5.55/1.11      ((~(![X1] : ((~r1_tarski(k1_relat_1(sK2),u1_struct_0(X1)) | (u1_struct_0(X1) = k1_relat_1(sK2)) | ~m1_yellow_0(X1,sK0))))) | (![X1] : ((~r1_tarski(k1_relat_1(sK2),u1_struct_0(X1)) | (u1_struct_0(X1) = k1_relat_1(sK2)) | ~m1_yellow_0(X1,sK0)))))).
% 5.55/1.11  
% 5.55/1.12  tff(u3575,axiom,
% 5.55/1.12      ((~(![X18, X20, X19] : ((~r1_tarski(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X18,X19)) | (k2_zfmisc_1(X18,X19) = k2_zfmisc_1(X18,X20)) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20))))) | (![X18, X20, X19] : ((~r1_tarski(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X18,X19)) | (k2_zfmisc_1(X18,X19) = k2_zfmisc_1(X18,X20)) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3574,negated_conjecture,
% 5.55/1.12      ((~~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2)) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2))).
% 5.55/1.12  
% 5.55/1.12  tff(u3573,negated_conjecture,
% 5.55/1.12      ((~~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),sK2)) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),sK2))).
% 5.55/1.12  
% 5.55/1.12  tff(u3572,negated_conjecture,
% 5.55/1.12      ((~(![X4] : ((~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X4),sK2) | (sK2 = k2_zfmisc_1(k1_relat_1(sK2),X4)) | ~r1_tarski(k2_relat_1(sK2),X4))))) | (![X4] : ((~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X4),sK2) | (sK2 = k2_zfmisc_1(k1_relat_1(sK2),X4)) | ~r1_tarski(k2_relat_1(sK2),X4)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3571,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,X23),sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) | (sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))) = k2_zfmisc_1(X21,X23)) | (k1_xboole_0 = k2_zfmisc_1(X21,X22)))))) | (![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,X23),sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) | (sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))) = k2_zfmisc_1(X21,X23)) | (k1_xboole_0 = k2_zfmisc_1(X21,X22))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3570,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23))),sK5(k2_zfmisc_1(X21,X22),X23)) | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23) | (sK5(k2_zfmisc_1(X21,X22),X23) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23))))) | (![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23))),sK5(k2_zfmisc_1(X21,X22),X23)) | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23) | (sK5(k2_zfmisc_1(X21,X22),X23) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3569,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23))) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23)) | (sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23))))) | r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)),X23))))) | (![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23))) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23)) | (sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)) = k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23))))) | r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(X23)),X23)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3568,axiom,
% 5.55/1.12      ((~(![X29, X31, X28, X30] : ((~r1_tarski(k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))) | (sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))) | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X30))))) | (![X29, X31, X28, X30] : ((~r1_tarski(k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))) | (sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X28,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))) | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X30)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3567,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | (k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))) | (![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | (k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3566,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))) | (![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X21,X23),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k2_zfmisc_1(X21,X23) = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3565,axiom,
% 5.55/1.12      ((~(![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))) | (![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3564,axiom,
% 5.55/1.12      ((~(![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,X45,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))) | (![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X42,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X44,X45,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X42,X46)) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3563,axiom,
% 5.55/1.12      ((~(![X29, X31, X28, X30] : ((~r1_tarski(k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))) | (sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))) | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28))))) | (![X29, X31, X28, X30] : ((~r1_tarski(k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))),sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))) | (sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))) = k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))) | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3562,axiom,
% 5.55/1.12      ((~(![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))))) | (![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3561,axiom,
% 5.55/1.12      ((~(![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,X43,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))) | (![X42, X44, X46, X43, X45] : ((~r1_tarski(k2_zfmisc_1(X44,X46),sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))),X46) | (k2_relat_1(sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45)))) = k2_relset_1(X42,X43,sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))))) | (sK5(k2_zfmisc_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(X44,X45))) = k2_zfmisc_1(X44,X46)) | (k1_zfmisc_1(k2_zfmisc_1(X42,X43)) = k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3560,axiom,
% 5.55/1.12      ((~(![X25, X23, X24] : ((~r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | (sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))))) | (![X25, X23, X24] : ((~r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | (sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3559,axiom,
% 5.55/1.12      ((~(![X25, X23, X24] : ((~r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | (sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))))) | (![X25, X23, X24] : ((~r1_tarski(k2_zfmisc_1(X23,X25),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),X25) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | (sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) = k2_zfmisc_1(X23,X25)) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3558,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))),sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21)) | (sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) = k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))) | r1_tarski(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X21))))) | (![X22, X21, X23] : ((~r1_tarski(k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))),sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21)) | (sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) = k2_zfmisc_1(X22,k2_relat_1(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))) | r1_tarski(sK5(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X21)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3557,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | (u1_struct_0(X0) = u1_struct_0(X1)) | ~m1_yellow_0(X0,X1))))) | (![X1, X0] : ((~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | (u1_struct_0(X0) = u1_struct_0(X1)) | ~m1_yellow_0(X0,X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3556,negated_conjecture,
% 5.55/1.12      ((~(![X0] : ((~r1_tarski(u1_struct_0(X0),k1_relat_1(sK2)) | ~l1_orders_2(X0) | (u1_struct_0(X0) = k1_relat_1(sK2)) | ~m1_yellow_0(sK0,X0))))) | (![X0] : ((~r1_tarski(u1_struct_0(X0),k1_relat_1(sK2)) | ~l1_orders_2(X0) | (u1_struct_0(X0) = k1_relat_1(sK2)) | ~m1_yellow_0(sK0,X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3555,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))) | (![X1, X0] : ((~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3554,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | (u1_orders_2(X1) = u1_orders_2(X0)) | ~m1_yellow_0(X0,X1))))) | (![X1, X0] : ((~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | (u1_orders_2(X1) = u1_orders_2(X0)) | ~m1_yellow_0(X0,X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3553,negated_conjecture,
% 5.55/1.12      ((~~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3552,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)) | ~r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0))))) | (![X1, X0] : ((~r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)) | ~r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3551,axiom,
% 5.55/1.12      ((~(![X5, X7, X6] : ((~r1_tarski(sK5(k2_zfmisc_1(X5,X6),X7),k2_zfmisc_1(X5,X6)) | (k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)),sK5(k2_zfmisc_1(X5,X6),X7))) | (k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7))))) | (![X5, X7, X6] : ((~r1_tarski(sK5(k2_zfmisc_1(X5,X6),X7),k2_zfmisc_1(X5,X6)) | (k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)) = k2_relset_1(X5,k2_relat_1(sK5(k2_zfmisc_1(X5,X6),X7)),sK5(k2_zfmisc_1(X5,X6),X7))) | (k1_zfmisc_1(k2_zfmisc_1(X5,X6)) = X7)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3550,axiom,
% 5.55/1.12      ((~(![X1] : (r1_tarski(X1,X1)))) | (![X1] : (r1_tarski(X1,X1))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3549,axiom,
% 5.55/1.12      ((~(![X0] : (r1_tarski(k1_xboole_0,X0)))) | (![X0] : (r1_tarski(k1_xboole_0,X0))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3548,axiom,
% 5.55/1.12      ((~(![X0] : ((r1_tarski(sK3(k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = X0))))) | (![X0] : ((r1_tarski(sK3(k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3547,axiom,
% 5.55/1.12      ((~(![X2] : ((r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)) | (k1_xboole_0 = sK5(X2,k1_zfmisc_1(k1_xboole_0))))))) | (![X2] : ((r1_tarski(sK5(X2,k1_zfmisc_1(k1_xboole_0)),X2) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X2)) | (k1_xboole_0 = sK5(X2,k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3546,axiom,
% 5.55/1.12      ((~(![X5] : ((r1_tarski(sK5(X5,k1_zfmisc_1(k1_xboole_0)),X5) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X5)) | v1_xboole_0(sK5(X5,k1_zfmisc_1(k1_xboole_0))))))) | (![X5] : ((r1_tarski(sK5(X5,k1_zfmisc_1(k1_xboole_0)),X5) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X5)) | v1_xboole_0(sK5(X5,k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3545,axiom,
% 5.55/1.12      ((~(![X11, X10, X12] : ((r1_tarski(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(X12)) | (k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))))) | (![X11, X10, X12] : ((r1_tarski(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(X12)) | (k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relset_1(X10,k2_relat_1(sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))),sK5(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3544,axiom,
% 5.55/1.12      ((~(![X13, X15, X14] : ((r1_tarski(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X13) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(X13)) | (k2_relset_1(X14,X15,sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relat_1(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))))))) | (![X13, X15, X14] : ((r1_tarski(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X13) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(X13)) | (k2_relset_1(X14,X15,sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relat_1(sK5(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3543,axiom,
% 5.55/1.12      ((~(![X20, X19, X21] : ((r1_tarski(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X19) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(X19)) | v1_relat_1(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))))) | (![X20, X19, X21] : ((r1_tarski(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X19) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(X19)) | v1_relat_1(sK5(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3542,axiom,
% 5.55/1.12      ((~(![X0] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)))))) | (![X0] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3541,axiom,
% 5.55/1.12      ((~(![X0] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)))))) | (![X0] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(X0)),X0) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3540,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1) | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)))))) | (![X1, X0] : ((r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X1) | r1_tarski(sK5(X0,k1_zfmisc_1(X1)),X0) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3539,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((r1_tarski(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)),X2) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)))))) | (![X1, X0, X2] : ((r1_tarski(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)),X2) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3538,axiom,
% 5.55/1.12      ((~(![X13, X12, X14] : ((r1_tarski(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14)),X14) | (k1_zfmisc_1(X14) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | (k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14)))))))) | (![X13, X12, X14] : ((r1_tarski(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14)),X14) | (k1_zfmisc_1(X14) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | (k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(X14))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3537,axiom,
% 5.55/1.12      ((~(![X18, X20, X19] : ((r1_tarski(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20)),X20) | (k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | v1_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20))))))) | (![X18, X20, X19] : ((r1_tarski(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20)),X20) | (k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | v1_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(X20)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3536,negated_conjecture,
% 5.55/1.12      ((~(![X2] : ((r1_tarski(u1_struct_0(X2),k1_relat_1(sK2)) | ~m1_yellow_0(X2,sK0))))) | (![X2] : ((r1_tarski(u1_struct_0(X2),k1_relat_1(sK2)) | ~m1_yellow_0(X2,sK0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3535,axiom,
% 5.55/1.12      ((~(![X18, X20, X19] : ((r1_tarski(k2_zfmisc_1(X18,X19),k2_zfmisc_1(X18,X20)) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20))))) | (![X18, X20, X19] : ((r1_tarski(k2_zfmisc_1(X18,X19),k2_zfmisc_1(X18,X20)) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X18,X19)),X20)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3534,negated_conjecture,
% 5.55/1.12      ((~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3533,negated_conjecture,
% 5.55/1.12      ((~(![X6] : ((r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X6)) | ~r1_tarski(k2_relat_1(sK2),X6))))) | (![X6] : ((r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X6)) | ~r1_tarski(k2_relat_1(sK2),X6)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3532,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23)) | (k1_xboole_0 = k2_zfmisc_1(X21,X22)) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23))))) | (![X22, X21, X23] : ((r1_tarski(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23)) | (k1_xboole_0 = k2_zfmisc_1(X21,X22)) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3531,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X21,X22),X23),k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23) | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23))))) | (![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X21,X22),X23),k2_zfmisc_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = X23) | r2_hidden(sK5(k2_zfmisc_1(X21,X22),X23),X23)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3530,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),k2_zfmisc_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21))))) | r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),X21) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21)))))) | (![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),k2_zfmisc_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21))))) | r1_tarski(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(X21)),X21) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(X21))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3529,axiom,
% 5.55/1.12      ((~(![X29, X31, X28, X30] : ((r1_tarski(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))) | v4_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))) | (![X29, X31, X28, X30] : ((r1_tarski(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))) | v4_relat_1(sK5(k2_zfmisc_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3528,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23)) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | (k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))))))) | (![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23)) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | (k1_xboole_0 = sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3527,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23)) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))))))) | (![X22, X21, X23] : ((r1_tarski(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)),k2_zfmisc_1(X21,X23)) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0))),X23) | v1_xboole_0(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3526,axiom,
% 5.55/1.12      ((~(![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39)) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39) | (k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))))) | (![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39)) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39) | (k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3525,axiom,
% 5.55/1.12      ((~(![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39)) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39) | (k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,X38,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))))) | (![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X35,X39)) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39) | (k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X37,X38,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3524,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23)) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))) | (![X22, X21, X23] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23)) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3523,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23)) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))) | (![X22, X21, X23] : ((r1_tarski(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,X23)) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))),X23) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3522,axiom,
% 5.55/1.12      ((~(![X22, X21, X23] : ((r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,k2_relat_1(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))) | r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X23) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23)))))) | (![X22, X21, X23] : ((r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),k2_zfmisc_1(X21,k2_relat_1(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))) | r1_tarski(sK5(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X23) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(X23))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3521,axiom,
% 5.55/1.12      ((~(![X29, X31, X28, X30] : ((r1_tarski(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))) | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))) | (![X29, X31, X28, X30] : ((r1_tarski(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),k2_zfmisc_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))) | v4_relat_1(sK5(k2_zfmisc_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X28) | (k1_zfmisc_1(k2_zfmisc_1(X28,X29)) = k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3520,axiom,
% 5.55/1.12      ((~(![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k2_zfmisc_1(X35,X39)) | (k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),X39) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))) | (![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k2_zfmisc_1(X35,X39)) | (k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))),X39) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3519,axiom,
% 5.55/1.12      ((~(![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X37,X39)) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39) | (k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X35,X36,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))))) | (![X36, X38, X35, X37, X39] : ((r1_tarski(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38))),k2_zfmisc_1(X37,X39)) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))),X39) | (k2_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))) = k2_relset_1(X35,X36,sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3518,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0))))) | (![X1, X0] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3517,negated_conjecture,
% 5.55/1.12      ((~(![X3] : ((r1_tarski(k1_relat_1(sK2),u1_struct_0(X3)) | ~m1_yellow_0(sK0,X3) | ~l1_orders_2(X3))))) | (![X3] : ((r1_tarski(k1_relat_1(sK2),u1_struct_0(X3)) | ~m1_yellow_0(sK0,X3) | ~l1_orders_2(X3)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3516,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0))))) | (![X1, X0] : ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3515,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))))) | (![X1, X0] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3514,axiom,
% 5.55/1.12      ((~(![X0] : (r1_xboole_0(X0,k1_xboole_0)))) | (![X0] : (r1_xboole_0(X0,k1_xboole_0))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3513,axiom,
% 5.55/1.12      ((~(![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))) | (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3512,negated_conjecture,
% 5.55/1.12      ((~~v1_xboole_0(k1_relat_1(sK2))) | ~v1_xboole_0(k1_relat_1(sK2)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3511,axiom,
% 5.55/1.12      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3510,axiom,
% 5.55/1.12      ((~(![X13, X12] : ((v1_xboole_0(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | (k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0)))))))) | (![X13, X12] : ((v1_xboole_0(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | (k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k1_xboole_0))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3509,axiom,
% 5.55/1.12      ((~(![X7, X6] : ((v1_xboole_0(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | (k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0)))))))) | (![X7, X6] : ((v1_xboole_0(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | (k2_relset_1(X6,X7,sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK5(k2_zfmisc_1(X6,X7),k1_zfmisc_1(k1_xboole_0))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3508,axiom,
% 5.55/1.12      ((~(![X11, X12] : ((v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X11,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))) | (![X11, X12] : ((v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) = k2_relset_1(X11,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))),sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3507,axiom,
% 5.55/1.12      ((~(![X7, X6] : ((v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | (k2_relset_1(X6,X7,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))))) | (![X7, X6] : ((v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | (k2_relset_1(X6,X7,sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) = k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3506,axiom,
% 5.55/1.12      ((~(![X3, X0] : ((~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0))))) | (![X3, X0] : ((~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3505,axiom,
% 5.55/1.12      ((~(![X0] : ((~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) | (k1_xboole_0 = X0))))) | (![X0] : ((~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) | (k1_xboole_0 = X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3504,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~r2_hidden(sK5(X0,X1),X1) | ~r1_tarski(sK5(X0,X1),X0) | (k1_zfmisc_1(X0) = X1))))) | (![X1, X0] : ((~r2_hidden(sK5(X0,X1),X1) | ~r1_tarski(sK5(X0,X1),X0) | (k1_zfmisc_1(X0) = X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3503,axiom,
% 5.55/1.12      ((~(![X3, X0] : ((r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0))))) | (![X3, X0] : ((r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3502,axiom,
% 5.55/1.12      ((~(![X0] : ((r2_hidden(sK3(X0),X0) | (k1_xboole_0 = k3_tarski(X0)))))) | (![X0] : ((r2_hidden(sK3(X0),X0) | (k1_xboole_0 = k3_tarski(X0))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3501,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((r2_hidden(sK5(X0,X1),X1) | r1_tarski(sK5(X0,X1),X0) | (k1_zfmisc_1(X0) = X1))))) | (![X1, X0] : ((r2_hidden(sK5(X0,X1),X1) | r1_tarski(sK5(X0,X1),X0) | (k1_zfmisc_1(X0) = X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3500,axiom,
% 5.55/1.12      ((~(![X2] : ((r2_hidden(sK5(k1_xboole_0,X2),X2) | (k1_zfmisc_1(k1_xboole_0) = X2) | (k1_xboole_0 = sK5(k1_xboole_0,X2)))))) | (![X2] : ((r2_hidden(sK5(k1_xboole_0,X2),X2) | (k1_zfmisc_1(k1_xboole_0) = X2) | (k1_xboole_0 = sK5(k1_xboole_0,X2))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3499,axiom,
% 5.55/1.12      ((~(![X3] : ((r2_hidden(sK5(k1_xboole_0,X3),X3) | (k1_zfmisc_1(k1_xboole_0) = X3) | v1_xboole_0(sK5(k1_xboole_0,X3)))))) | (![X3] : ((r2_hidden(sK5(k1_xboole_0,X3),X3) | (k1_zfmisc_1(k1_xboole_0) = X3) | v1_xboole_0(sK5(k1_xboole_0,X3))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3498,axiom,
% 5.55/1.12      ((~(![X11, X10, X12] : ((r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12) | (k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)) = k2_relset_1(X10,k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)),sK5(k2_zfmisc_1(X10,X11),X12))))))) | (![X11, X10, X12] : ((r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12) | (k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)) = k2_relset_1(X10,k2_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)),sK5(k2_zfmisc_1(X10,X11),X12)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3497,axiom,
% 5.55/1.12      ((~(![X5, X4, X6] : ((r2_hidden(sK5(k2_zfmisc_1(X4,X5),X6),X6) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = X6) | (k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),X6)) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),X6))))))) | (![X5, X4, X6] : ((r2_hidden(sK5(k2_zfmisc_1(X4,X5),X6),X6) | (k1_zfmisc_1(k2_zfmisc_1(X4,X5)) = X6) | (k2_relset_1(X4,X5,sK5(k2_zfmisc_1(X4,X5),X6)) = k2_relat_1(sK5(k2_zfmisc_1(X4,X5),X6)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3496,axiom,
% 5.55/1.12      ((~(![X11, X10, X12] : ((r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12) | v1_relat_1(sK5(k2_zfmisc_1(X10,X11),X12)))))) | (![X11, X10, X12] : ((r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12) | v1_relat_1(sK5(k2_zfmisc_1(X10,X11),X12))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3495,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))) | (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3494,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k1_xboole_0 = X1) | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k1_xboole_0 = X1) | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3493,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))) | (![X1, X3, X0, X2] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3492,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3491,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k2_relset_1(X0,X1,X2) = k2_relat_1(X2)))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k2_relset_1(X0,X1,X2) = k2_relat_1(X2))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3490,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3489,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3488,axiom,
% 5.55/1.12      ((~(![X1, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2))))) | (![X1, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3487,negated_conjecture,
% 5.55/1.12      ((~~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3486,negated_conjecture,
% 5.55/1.12      ((~~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3485,negated_conjecture,
% 5.55/1.12      ((~~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3484,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))) | (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3483,axiom,
% 5.55/1.12      ((~(![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))) | (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3482,axiom,
% 5.55/1.12      ((~(![X3, X5, X4] : ((m1_subset_1(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X5))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X3,X4)),X5))))) | (![X3, X5, X4] : ((m1_subset_1(k2_zfmisc_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X5))) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X3,X4)),X5)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3481,negated_conjecture,
% 5.55/1.12      ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3480,negated_conjecture,
% 5.55/1.12      ((~(![X6] : ((m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X6))) | ~r1_tarski(k2_relat_1(sK2),X6))))) | (![X6] : ((m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X6))) | ~r1_tarski(k2_relat_1(sK2),X6)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3479,axiom,
% 5.55/1.12      ((~(![X9, X8, X10] : ((m1_subset_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),k1_zfmisc_1(k2_zfmisc_1(X8,X10))) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))),X10) | (k1_xboole_0 = k2_zfmisc_1(X8,X9)))))) | (![X9, X8, X10] : ((m1_subset_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),k1_zfmisc_1(k2_zfmisc_1(X8,X10))) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))),X10) | (k1_xboole_0 = k2_zfmisc_1(X8,X9))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3478,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))))) | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2))))) | (![X1, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))))) | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3477,axiom,
% 5.55/1.12      ((~(![X1, X3, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3))))) | (![X1, X3, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3476,axiom,
% 5.55/1.12      ((~(![X1, X3, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3))))) | (![X1, X3, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(k1_xboole_0))),X3)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3475,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0))))) | (![X1, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3474,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0))))) | (![X1, X3, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3473,axiom,
% 5.55/1.12      ((~(![X18, X20, X17, X19, X21] : ((m1_subset_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))),k1_zfmisc_1(k2_zfmisc_1(X19,X21))) | (k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))) = k2_relset_1(X17,k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))))) | (k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),X21))))) | (![X18, X20, X17, X19, X21] : ((m1_subset_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))),k1_zfmisc_1(k2_zfmisc_1(X19,X21))) | (k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))) = k2_relset_1(X17,k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18))))) | (k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))),X21)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3472,axiom,
% 5.55/1.12      ((~(![X16, X13, X15, X17, X14] : ((m1_subset_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),k1_zfmisc_1(k2_zfmisc_1(X15,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | (k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X17))))) | (![X16, X13, X15, X17, X14] : ((m1_subset_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),k1_zfmisc_1(k2_zfmisc_1(X15,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,X14,sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | (k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),X17)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3471,axiom,
% 5.55/1.12      ((~(![X3, X2, X4] : ((m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4))))) | (![X3, X2, X4] : ((m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3470,axiom,
% 5.55/1.12      ((~(![X1, X3, X2] : ((m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3))))) | (![X1, X3, X2] : ((m1_subset_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X3)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3469,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((m1_subset_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)) | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2))))) | (![X1, X0, X2] : ((m1_subset_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)) | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3468,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0))))) | (![X1, X3, X0, X2] : ((m1_subset_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3467,axiom,
% 5.55/1.12      ((~(![X16, X18, X20, X17, X19] : ((m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),k1_zfmisc_1(k2_zfmisc_1(X18,X20))) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20))))) | (![X16, X18, X20, X17, X19] : ((m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),k1_zfmisc_1(k2_zfmisc_1(X18,X20))) | (k1_zfmisc_1(k2_zfmisc_1(X18,X19)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relset_1(X16,k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))),X20)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3466,axiom,
% 5.55/1.12      ((~(![X16, X18, X15, X17, X14] : ((m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),k1_zfmisc_1(k2_zfmisc_1(X14,X18))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),X18))))) | (![X16, X18, X15, X17, X14] : ((m1_subset_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),k1_zfmisc_1(k2_zfmisc_1(X14,X18))) | (k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X16,X17,sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),X18)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3465,axiom,
% 5.55/1.12      ((~v1_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3464,axiom,
% 5.55/1.12      ((~(![X1, X0] : (v1_relat_1(k2_zfmisc_1(X0,X1))))) | (![X1, X0] : (v1_relat_1(k2_zfmisc_1(X0,X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3463,negated_conjecture,
% 5.55/1.12      ((~v1_relat_1(sK2)) | v1_relat_1(sK2))).
% 5.55/1.12  
% 5.55/1.12  tff(u3462,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (k1_xboole_0 = k2_zfmisc_1(X0,X1)))))) | (![X1, X0] : ((v1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (k1_xboole_0 = k2_zfmisc_1(X0,X1))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3461,axiom,
% 5.55/1.12      ((~(![X11, X10] : ((v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))) | (![X11, X10] : ((v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3460,axiom,
% 5.55/1.12      ((~(![X11, X10] : ((v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))) | (![X11, X10] : ((v1_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | v1_xboole_0(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3459,axiom,
% 5.55/1.12      ((~(![X32, X31, X33, X30] : ((v1_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) | (k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))) | (![X32, X31, X33, X30] : ((v1_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) | (k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3458,axiom,
% 5.55/1.12      ((~(![X11, X12] : ((v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))))) | (![X11, X12] : ((v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3457,axiom,
% 5.55/1.12      ((~(![X11, X10] : ((v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))))) | (![X11, X10] : ((v1_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3456,negated_conjecture,
% 5.55/1.12      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3455,axiom,
% 5.55/1.12      ((~~v1_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3454,negated_conjecture,
% 5.55/1.12      ((~v1_funct_1(sK2)) | v1_funct_1(sK2))).
% 5.55/1.12  
% 5.55/1.12  tff(u3453,axiom,
% 5.55/1.12      ((~(![X1] : ((~v4_relat_1(X1,k1_relat_1(X1)) | v1_partfun1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1))))) | (![X1] : ((~v4_relat_1(X1,k1_relat_1(X1)) | v1_partfun1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3452,axiom,
% 5.55/1.12      ((~(![X0] : (v4_relat_1(k1_xboole_0,X0)))) | (![X0] : (v4_relat_1(k1_xboole_0,X0))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3451,axiom,
% 5.55/1.12      ((~(![X1, X0] : (v4_relat_1(k2_zfmisc_1(X0,X1),X0)))) | (![X1, X0] : (v4_relat_1(k2_zfmisc_1(X0,X1),X0))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3450,negated_conjecture,
% 5.55/1.12      ((~v4_relat_1(sK2,k1_relat_1(sK2))) | v4_relat_1(sK2,k1_relat_1(sK2)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3449,axiom,
% 5.55/1.12      ((~(![X3, X4] : ((v4_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) | (k1_xboole_0 = k2_zfmisc_1(X3,X4)))))) | (![X3, X4] : ((v4_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X3) | (k1_xboole_0 = k2_zfmisc_1(X3,X4))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3448,axiom,
% 5.55/1.12      ((~(![X9, X7, X8] : ((v4_relat_1(sK5(k2_zfmisc_1(X7,X8),X9),X7) | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9))))) | (![X9, X7, X8] : ((v4_relat_1(sK5(k2_zfmisc_1(X7,X8),X9),X7) | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3447,axiom,
% 5.55/1.12      ((~(![X9, X8] : ((v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8) | (k1_xboole_0 = sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9))))))) | (![X9, X8] : ((v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8) | (k1_xboole_0 = sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3446,axiom,
% 5.55/1.12      ((~(![X9, X8] : ((v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8) | v1_xboole_0(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9))))))) | (![X9, X8] : ((v4_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0)),X8) | v1_xboole_0(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3445,axiom,
% 5.55/1.12      ((~(![X16, X15, X17] : ((v4_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X15) | r1_tarski(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X17) | (k1_zfmisc_1(X17) = k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))) | (![X16, X15, X17] : ((v4_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X15) | r1_tarski(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(X17)),X17) | (k1_zfmisc_1(X17) = k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3444,axiom,
% 5.55/1.12      ((~(![X32, X31, X33, X30] : ((v4_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X32) | (k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) = k2_relset_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))) | (k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))) | (![X32, X31, X33, X30] : ((v4_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))),X32) | (k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))) = k2_relset_1(X30,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(X30,X31))))) | (k1_zfmisc_1(k2_zfmisc_1(X30,X31)) = k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3443,axiom,
% 5.55/1.12      ((~(![X25, X23, X24, X26] : ((v4_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X23) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | (k2_relset_1(X25,X26,sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) = k2_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))))) | (![X25, X23, X24, X26] : ((v4_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X23) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | (k2_relset_1(X25,X26,sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) = k2_relat_1(sK5(k2_zfmisc_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3442,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2))))))) | (![X1, X0, X2] : ((v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X2)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3441,axiom,
% 5.55/1.12      ((~(![X9, X10] : ((v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))))) | (![X9, X10] : ((v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3440,axiom,
% 5.55/1.12      ((~(![X9, X8] : ((v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))))) | (![X9, X8] : ((v4_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X8,X9))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3439,axiom,
% 5.55/1.12      ((~(![X16, X18, X17] : ((v4_relat_1(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X17) | r1_tarski(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X16) | (k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(X16)))))) | (![X16, X18, X17] : ((v4_relat_1(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X17) | r1_tarski(sK5(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18))),X16) | (k1_zfmisc_1(k2_zfmisc_1(X17,X18)) = k1_zfmisc_1(X16))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3438,axiom,
% 5.55/1.12      ((~(![X18, X20, X19, X21] : ((v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | (k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))))) | (![X18, X20, X19, X21] : ((v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | (k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) = k2_relset_1(X18,k2_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))),sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3437,axiom,
% 5.55/1.12      ((~(![X22, X25, X23, X24] : ((v4_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X24) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))) | (k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))) = k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))))) | (![X22, X25, X23, X24] : ((v4_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X24) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))) | (k2_relset_1(X22,X23,sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))) = k2_relat_1(sK5(k2_zfmisc_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3436,axiom,
% 5.55/1.12      ((~(![X27, X29, X26, X28] : ((v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28) | v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X26) | (k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29))))))) | (![X27, X29, X26, X28] : ((v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X28) | v4_relat_1(sK5(k2_zfmisc_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X28,X29))),X26) | (k1_zfmisc_1(k2_zfmisc_1(X26,X27)) = k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3435,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~v1_partfun1(X1,X0) | (k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))))) | (![X1, X0] : ((~v1_partfun1(X1,X0) | (k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3434,axiom,
% 5.55/1.12      ((~(![X7, X8, X6] : ((~v1_partfun1(sK5(k2_zfmisc_1(X6,X7),X8),X6) | v1_funct_2(sK5(k2_zfmisc_1(X6,X7),X8),X6,X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X6,X7),X8)) | r2_hidden(sK5(k2_zfmisc_1(X6,X7),X8),X8) | (k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = X8))))) | (![X7, X8, X6] : ((~v1_partfun1(sK5(k2_zfmisc_1(X6,X7),X8),X6) | v1_funct_2(sK5(k2_zfmisc_1(X6,X7),X8),X6,X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X6,X7),X8)) | r2_hidden(sK5(k2_zfmisc_1(X6,X7),X8),X8) | (k1_zfmisc_1(k2_zfmisc_1(X6,X7)) = X8)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3433,axiom,
% 5.55/1.12      ((~(![X9, X11, X10] : ((~v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9) | (k1_zfmisc_1(X11) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11))) | v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9,X10) | r1_tarski(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X11))))) | (![X9, X11, X10] : ((~v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9) | (k1_zfmisc_1(X11) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11))) | v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X9,X10) | r1_tarski(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(X11)),X11)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3432,axiom,
% 5.55/1.12      ((~(![X18, X20, X19, X21] : ((~v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) | v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18,X19) | v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20))))) | (![X18, X20, X19, X21] : ((~v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) | v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X18,X19) | v4_relat_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3431,axiom,
% 5.55/1.12      ((~(![X11, X10, X12] : ((~v1_partfun1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(X10)) | ~v1_funct_1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | v1_funct_2(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X12) | r1_tarski(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X10))))) | (![X11, X10, X12] : ((~v1_partfun1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(X10)) | ~v1_funct_1(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | v1_funct_2(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,X12) | r1_tarski(sK5(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X10)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3430,axiom,
% 5.55/1.12      ((~(![X20, X22, X19, X21] : ((~v1_partfun1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21) | (k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~v1_funct_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | v1_funct_2(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21,X22) | v4_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X19))))) | (![X20, X22, X19, X21] : ((~v1_partfun1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21) | (k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~v1_funct_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))) | v1_funct_2(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X21,X22) | v4_relat_1(sK5(k2_zfmisc_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(X21,X22))),X19)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3429,axiom,
% 5.55/1.12      ((~v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))) | v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3428,negated_conjecture,
% 5.55/1.12      ((~v1_partfun1(sK2,k1_relat_1(sK2))) | v1_partfun1(sK2,k1_relat_1(sK2)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3427,negated_conjecture,
% 5.55/1.12      ((~~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3426,negated_conjecture,
% 5.55/1.12      ((~~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3425,axiom,
% 5.55/1.12      ((~(![X0] : ((~v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) | ~v1_funct_1(k2_zfmisc_1(k1_xboole_0,X0)) | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0))))) | (![X0] : ((~v1_funct_2(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0,X0) | ~v1_funct_1(k2_zfmisc_1(k1_xboole_0,X0)) | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3424,axiom,
% 5.55/1.12      ((~(![X16, X17] : ((~v1_funct_2(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0,X17) | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(k1_xboole_0,X16)),X17) | ~v1_funct_1(k2_zfmisc_1(k1_xboole_0,X16)))))) | (![X16, X17] : ((~v1_funct_2(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0,X17) | v1_partfun1(k2_zfmisc_1(k1_xboole_0,X16),k1_xboole_0) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(k1_xboole_0,X16)),X17) | ~v1_funct_1(k2_zfmisc_1(k1_xboole_0,X16))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3423,axiom,
% 5.55/1.12      ((~(![X5, X4] : ((~v1_funct_2(k2_zfmisc_1(X4,X5),X4,X5) | v1_partfun1(k2_zfmisc_1(X4,X5),X4) | ~v1_funct_1(k2_zfmisc_1(X4,X5)) | (k1_xboole_0 = X5))))) | (![X5, X4] : ((~v1_funct_2(k2_zfmisc_1(X4,X5),X4,X5) | v1_partfun1(k2_zfmisc_1(X4,X5),X4) | ~v1_funct_1(k2_zfmisc_1(X4,X5)) | (k1_xboole_0 = X5)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3422,axiom,
% 5.55/1.12      ((~(![X5, X7, X6] : ((~v1_funct_2(k2_zfmisc_1(X6,X7),X6,X5) | v1_partfun1(k2_zfmisc_1(X6,X7),X6) | (k1_xboole_0 = X5) | ~v1_funct_1(k2_zfmisc_1(X6,X7)) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X6,X7)),X5))))) | (![X5, X7, X6] : ((~v1_funct_2(k2_zfmisc_1(X6,X7),X6,X5) | v1_partfun1(k2_zfmisc_1(X6,X7),X6) | (k1_xboole_0 = X5) | ~v1_funct_1(k2_zfmisc_1(X6,X7)) | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X6,X7)),X5)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3421,negated_conjecture,
% 5.55/1.12      ((~~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3420,axiom,
% 5.55/1.12      ((~(![X2] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0,X2) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0) | (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)))))) | (![X2] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0,X2) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))),k1_xboole_0) | (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3419,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20) | (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X19)) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))))))) | (![X20, X19] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20) | (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X19)) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3418,axiom,
% 5.55/1.12      ((~(![X9, X8] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8,X9) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) | (k1_xboole_0 = X9) | (k1_xboole_0 = k2_zfmisc_1(X8,X9)))))) | (![X9, X8] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8,X9) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9))),X8) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) | (k1_xboole_0 = X9) | (k1_xboole_0 = k2_zfmisc_1(X8,X9))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3417,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2) | (k1_xboole_0 = k2_zfmisc_1(X0,X1)) | (k1_xboole_0 = X2) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2) | (k1_xboole_0 = k2_zfmisc_1(X0,X1)) | (k1_xboole_0 = X2) | v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~r1_tarski(k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3416,axiom,
% 5.55/1.12      ((~(![X3, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0,X3) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4)) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0) | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),X4) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)) = X4))))) | (![X3, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0,X3) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4)) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),k1_xboole_0) | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X3),X4),X4) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)) = X4)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3415,axiom,
% 5.55/1.12      ((~(![X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12) | (k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0))))) | (![X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12) | (k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3414,axiom,
% 5.55/1.12      ((~(![X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12) | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0))))) | (![X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X12) | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X12),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3413,axiom,
% 5.55/1.12      ((~(![X22, X21] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0,X21) | (k1_zfmisc_1(X22) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X21))) | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),X22) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0))))) | (![X22, X21] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0,X21) | (k1_zfmisc_1(X22) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X21))) | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),X22) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X21),k1_zfmisc_1(X22)),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3412,axiom,
% 5.55/1.12      ((~(![X40, X38, X39] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0,X40) | (k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))) = k2_relset_1(X38,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))),sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))))) | (k1_zfmisc_1(k2_zfmisc_1(X38,X39)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X40))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0))))) | (![X40, X38, X39] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0,X40) | (k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))) = k2_relset_1(X38,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))),sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))))) | (k1_zfmisc_1(k2_zfmisc_1(X38,X39)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X40))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X40),k1_zfmisc_1(k2_zfmisc_1(X38,X39))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3411,axiom,
% 5.55/1.12      ((~(![X34, X36, X35] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36) | (k2_relset_1(X34,X35,sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))) | (k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0))))) | (![X34, X36, X35] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36) | (k2_relset_1(X34,X35,sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))))) | (k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3410,axiom,
% 5.55/1.12      ((~(![X34, X36, X35] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X34))) | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),X35) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0))))) | (![X34, X36, X35] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X34))) | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),X35) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X34),k1_zfmisc_1(k2_zfmisc_1(X35,X36))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3409,axiom,
% 5.55/1.12      ((~(![X34, X36, X35] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36) | v1_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) | (k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0))))) | (![X34, X36, X35] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0,X36) | v1_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) | (k1_zfmisc_1(k2_zfmisc_1(X34,X35)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X36))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X36),k1_zfmisc_1(k2_zfmisc_1(X34,X35))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3408,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | (k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))))))) | (![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | (k1_xboole_0 = sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3407,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))))))) | (![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0,X20) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))),X20) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) | v1_xboole_0(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3406,axiom,
% 5.55/1.12      ((~(![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0) | (k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))))) | (![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0) | (k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3405,axiom,
% 5.55/1.12      ((~(![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0) | (k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,X33,sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))))) | (![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))),k1_xboole_0) | (k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))) = k2_relset_1(X32,X33,sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X31),k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3404,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20))) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)) = X20) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0) | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),X20) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20)))))) | (![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20))) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)) = X20) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),k1_xboole_0) | r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20),X20) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X19),X20))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3403,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)))) | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),X19) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0) | (k1_zfmisc_1(X19) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X20))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19))))))) | (![X20, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)))) | r1_tarski(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),X19) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)),k1_xboole_0) | (k1_zfmisc_1(X19) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X20))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X20),k1_zfmisc_1(X19)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3402,axiom,
% 5.55/1.12      ((~(![X25, X27, X26] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))))) | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))))) | (![X25, X27, X26] : ((~v1_funct_2(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))))) | v4_relat_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25) | v1_partfun1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))),k1_xboole_0) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))) | ~v1_funct_1(sK5(k2_zfmisc_1(k1_xboole_0,X27),k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3401,axiom,
% 5.55/1.12      ((~(![X38, X37, X39] : ((~v1_funct_2(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0,X39) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | (k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))) | v1_partfun1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0))))) | (![X38, X37, X39] : ((~v1_funct_2(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0,X39) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)) = k1_zfmisc_1(k2_zfmisc_1(X37,X38))) | (k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))) = k2_relset_1(X37,k2_relat_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))),sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39)))) | v1_partfun1(sK5(k2_zfmisc_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X39))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3400,axiom,
% 5.55/1.12      ((~(![X36, X35, X37] : ((~v1_funct_2(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0,X35) | (k2_relset_1(X36,X37,sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))))) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)) = k1_zfmisc_1(k2_zfmisc_1(X36,X37))) | ~v1_funct_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)))) | v1_partfun1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0))))) | (![X36, X35, X37] : ((~v1_funct_2(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0,X35) | (k2_relset_1(X36,X37,sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)))) = k2_relat_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))))) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)) = k1_zfmisc_1(k2_zfmisc_1(X36,X37))) | ~v1_funct_1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35)))) | v1_partfun1(sK5(k2_zfmisc_1(X36,X37),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X35))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3399,axiom,
% 5.55/1.12      ((~(![X36, X35, X37] : ((~v1_funct_2(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0,X37) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))) | v4_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),X35) | ~v1_funct_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37)))) | v1_partfun1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0))))) | (![X36, X35, X37] : ((~v1_funct_2(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0,X37) | (k1_zfmisc_1(k2_zfmisc_1(X35,X36)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))) | v4_relat_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),X35) | ~v1_funct_1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37)))) | v1_partfun1(sK5(k2_zfmisc_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X37))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3398,axiom,
% 5.55/1.12      ((~(![X25, X27, X26] : ((~v1_funct_2(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))))) | v4_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),X25) | v1_partfun1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))) | ~v1_funct_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27)))))))) | (![X25, X27, X26] : ((~v1_funct_2(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0,k2_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))))) | v4_relat_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),X25) | v1_partfun1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))),k1_xboole_0) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))) | ~v1_funct_1(sK5(k2_zfmisc_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X27))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3397,axiom,
% 5.55/1.12      ((~(![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0,X34) | (k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0) | (k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))) | ~v1_funct_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))))))) | (![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0,X34) | (k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))) = k2_relset_1(X32,k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))),k1_xboole_0) | (k1_zfmisc_1(k2_zfmisc_1(X32,X33)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))) | ~v1_funct_1(sK5(k2_zfmisc_1(X32,X33),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X31))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3396,axiom,
% 5.55/1.12      ((~(![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X31,X32)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0) | (k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))) = k2_relset_1(X31,X32,sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))))))) | (![X32, X34, X31, X33] : ((~v1_funct_2(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0,X34) | (k1_zfmisc_1(k2_zfmisc_1(X31,X32)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))),X34) | v1_partfun1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))),k1_xboole_0) | (k2_relat_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33)))) = k2_relset_1(X31,X32,sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X33))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3395,axiom,
% 5.55/1.12      ((~(![X11, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X10,X11),X12),X10,X11) | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),X12),X10) | ~v1_funct_1(sK5(k2_zfmisc_1(X10,X11),X12)) | (k1_xboole_0 = X11) | r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12))))) | (![X11, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X10,X11),X12),X10,X11) | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),X12),X10) | ~v1_funct_1(sK5(k2_zfmisc_1(X10,X11),X12)) | (k1_xboole_0 = X11) | r2_hidden(sK5(k2_zfmisc_1(X10,X11),X12),X12) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = X12)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3394,axiom,
% 5.55/1.12      ((~(![X16, X17] : ((~v1_funct_2(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16,X17) | v1_partfun1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16) | ~v1_funct_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = X17) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0))))))) | (![X16, X17] : ((~v1_funct_2(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16,X17) | v1_partfun1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)),X16) | ~v1_funct_1(sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = X17) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X16,X17),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3393,axiom,
% 5.55/1.12      ((~(![X18, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18,X19) | v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18) | ~v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = X19) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | v1_xboole_0(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0))))))) | (![X18, X19] : ((~v1_funct_2(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18,X19) | v1_partfun1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)),X18) | ~v1_funct_1(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = X19) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | v1_xboole_0(sK5(k2_zfmisc_1(X18,X19),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3392,axiom,
% 5.55/1.12      ((~(![X13, X15, X14] : ((~v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13,X14) | v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13) | ~v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15))) | (k1_xboole_0 = X14) | r1_tarski(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X15) | (k1_zfmisc_1(X15) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))))))) | (![X13, X15, X14] : ((~v1_funct_2(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13,X14) | v1_partfun1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X13) | ~v1_funct_1(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15))) | (k1_xboole_0 = X14) | r1_tarski(sK5(k2_zfmisc_1(X13,X14),k1_zfmisc_1(X15)),X15) | (k1_zfmisc_1(X15) = k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3391,axiom,
% 5.55/1.12      ((~(![X16, X13, X15, X14] : ((~v1_funct_2(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15,X16) | (k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | v1_partfun1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_funct_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | (k1_xboole_0 = X16))))) | (![X16, X13, X15, X14] : ((~v1_funct_2(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15,X16) | (k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) = k2_relset_1(X13,k2_relat_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))))) | v1_partfun1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14))),X15) | (k1_zfmisc_1(k2_zfmisc_1(X15,X16)) = k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_funct_1(sK5(k2_zfmisc_1(X15,X16),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) | (k1_xboole_0 = X16)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3390,axiom,
% 5.55/1.12      ((~(![X9, X11, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,X12) | (k2_relset_1(X9,X10,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))) | v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) | (k1_xboole_0 = X12))))) | (![X9, X11, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,X12) | (k2_relset_1(X9,X10,sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) = k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))) | v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) | (k1_xboole_0 = X12)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3389,axiom,
% 5.55/1.12      ((~(![X9, X11, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9,X10) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9) | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k1_xboole_0 = X10))))) | (![X9, X11, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9,X10) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9) | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k1_xboole_0 = X10)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3388,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | (k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | (k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3387,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3386,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))) | (![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3385,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))) | (![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,X4) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3384,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),X2),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),X2),X0) | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),X2)))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),X2),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),X2))) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),X2),X0) | r2_hidden(sK5(k2_zfmisc_1(X0,X1),X2),X2) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),X2))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3383,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))) | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))) | v1_partfun1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1,k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))) | r1_tarski(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))) | v1_partfun1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(sK5(k2_zfmisc_1(X1,X2),k1_zfmisc_1(X0)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3382,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X3, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | v4_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3381,axiom,
% 5.55/1.12      ((~(![X13, X15, X12, X14] : ((~v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14,X15) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14) | (k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) | (k1_xboole_0 = X15))))) | (![X13, X15, X12, X14] : ((~v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14,X15) | (k1_zfmisc_1(k2_zfmisc_1(X14,X15)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))),X14) | (k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) = k2_relset_1(X12,k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))),sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) | (k1_xboole_0 = X15)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3380,axiom,
% 5.55/1.12      ((~(![X11, X13, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10,X11) | (k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))) | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_xboole_0 = X11))))) | (![X11, X13, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10,X11) | (k2_relset_1(X12,X13,sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) = k2_relat_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))))) | v1_partfun1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11))),X10) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_1(sK5(k2_zfmisc_1(X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) | (k1_xboole_0 = X11)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3379,axiom,
% 5.55/1.12      ((~(![X11, X13, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12,X13) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12) | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10) | ~v1_funct_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13)))) | (k1_xboole_0 = X13))))) | (![X11, X13, X10, X12] : ((~v1_funct_2(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12,X13) | (k1_zfmisc_1(k2_zfmisc_1(X10,X11)) = k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | v1_partfun1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X12) | v4_relat_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X10) | ~v1_funct_1(sK5(k2_zfmisc_1(X10,X11),k1_zfmisc_1(k2_zfmisc_1(X12,X13)))) | (k1_xboole_0 = X13)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3378,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))) | (![X1, X3, X0, X2] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | v4_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | (k1_xboole_0 = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3377,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X4) | (k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X4) | (k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK5(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3376,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,X4) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | (k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))) | (![X1, X3, X0, X2, X4] : ((~v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,X4) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r1_tarski(k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),X4) | (k1_xboole_0 = X4) | v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | (k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3375,axiom,
% 5.55/1.12      ((~(![X13] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0,X13) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0))))) | (![X13] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0,X13) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3374,axiom,
% 5.55/1.12      ((~(![X12] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0,X12) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0))))) | (![X12] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0,X12) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3373,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))))))) | (![X20, X19] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3372,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))))))) | (![X20, X19] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,X20) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))),X20) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3371,axiom,
% 5.55/1.12      ((~(![X20, X21] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20,X21) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) | (k1_xboole_0 = X21) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))) | (![X20, X21] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20,X21) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) | (k1_xboole_0 = X21) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3370,axiom,
% 5.55/1.12      ((~(![X22, X23] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22,X23) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_xboole_0 = X23) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X22,X23))))))) | (![X22, X23] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22,X23) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X22) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_xboole_0 = X23) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3369,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3368,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X2) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~r1_tarski(k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),X2) | (k1_xboole_0 = X2) | v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3367,axiom,
% 5.55/1.12      ((~(![X22, X23] : ((~v1_funct_2(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0,X23) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23)) = k1_zfmisc_1(X22)) | r1_tarski(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),X22) | ~v1_funct_1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23)))) | v1_partfun1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0))))) | (![X22, X23] : ((~v1_funct_2(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0,X23) | (k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23)) = k1_zfmisc_1(X22)) | r1_tarski(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),X22) | ~v1_funct_1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23)))) | v1_partfun1(sK5(X22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X23))),k1_xboole_0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3366,axiom,
% 5.55/1.12      ((~(![X20, X19] : ((~v1_funct_2(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,k2_relat_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))) | r1_tarski(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),X20) | v1_partfun1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | (k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~v1_funct_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19)))))))) | (![X20, X19] : ((~v1_funct_2(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0,k2_relat_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))) | r1_tarski(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),X20) | v1_partfun1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))),k1_xboole_0) | (k1_zfmisc_1(X20) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))) | ~v1_funct_1(sK5(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X19))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3365,axiom,
% 5.55/1.12      ((~(![X25, X24, X26] : ((~v1_funct_2(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25,X26) | v1_partfun1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25) | ~v1_funct_1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) | (k1_xboole_0 = X26) | r1_tarski(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X24) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(X24)))))) | (![X25, X24, X26] : ((~v1_funct_2(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25,X26) | v1_partfun1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X25) | ~v1_funct_1(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))) | (k1_xboole_0 = X26) | r1_tarski(sK5(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))),X24) | (k1_zfmisc_1(k2_zfmisc_1(X25,X26)) = k1_zfmisc_1(X24))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3364,axiom,
% 5.55/1.12      ((~(![X1, X0, X2] : ((~v1_funct_2(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) | (k1_xboole_0 = k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | v1_partfun1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)) | ~v1_funct_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0, X2] : ((~v1_funct_2(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | r1_tarski(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) | (k1_xboole_0 = k2_relat_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | v1_partfun1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)) | ~v1_funct_1(sK5(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3363,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(k2_zfmisc_1(X0,X1),X0,X1) | ~v1_funct_1(k2_zfmisc_1(X0,X1)) | ~v1_partfun1(k2_zfmisc_1(X0,X1),X0))))) | (![X1, X0] : ((v1_funct_2(k2_zfmisc_1(X0,X1),X0,X1) | ~v1_funct_1(k2_zfmisc_1(X0,X1)) | ~v1_partfun1(k2_zfmisc_1(X0,X1),X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3362,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(k2_zfmisc_1(X0,X1),X0,k2_relat_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(k2_zfmisc_1(X0,X1)) | ~v1_partfun1(k2_zfmisc_1(X0,X1),X0))))) | (![X1, X0] : ((v1_funct_2(k2_zfmisc_1(X0,X1),X0,k2_relat_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(k2_zfmisc_1(X0,X1)) | ~v1_partfun1(k2_zfmisc_1(X0,X1),X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3361,negated_conjecture,
% 5.55/1.12      ((~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)))).
% 5.55/1.12  
% 5.55/1.12  tff(u3360,negated_conjecture,
% 5.55/1.12      ((~(![X2] : ((v1_funct_2(sK2,k1_relat_1(sK2),X2) | ~r1_tarski(k2_relat_1(sK2),X2))))) | (![X2] : ((v1_funct_2(sK2,k1_relat_1(sK2),X2) | ~r1_tarski(k2_relat_1(sK2),X2)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3359,axiom,
% 5.55/1.12      ((~(![X5, X4] : ((v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | ~v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4) | (k1_xboole_0 = k2_zfmisc_1(X4,X5)))))) | (![X5, X4] : ((v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | ~v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4) | (k1_xboole_0 = k2_zfmisc_1(X4,X5))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3358,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | ~v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (k1_xboole_0 = k2_zfmisc_1(X0,X1)))))) | (![X1, X0] : ((v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | ~v1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (k1_xboole_0 = k2_zfmisc_1(X0,X1))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3357,axiom,
% 5.55/1.12      ((~(![X5, X4] : ((v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5) | (k1_xboole_0 = sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4))))) | (![X5, X4] : ((v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5) | (k1_xboole_0 = sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3356,axiom,
% 5.55/1.12      ((~(![X5, X4] : ((v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5) | v1_xboole_0(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4))))) | (![X5, X4] : ((v1_funct_2(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4,X5) | v1_xboole_0(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | ~v1_funct_1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK5(k2_zfmisc_1(X4,X5),k1_zfmisc_1(k1_xboole_0)),X4)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3355,axiom,
% 5.55/1.12      ((~(![X22, X25, X23, X24] : ((v1_funct_2(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24,X25) | (k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))),sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))) | ~v1_partfun1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24))))) | (![X22, X25, X23, X24] : ((v1_funct_2(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24,X25) | (k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) = k2_relset_1(X22,k2_relat_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))),sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))) | (k1_zfmisc_1(k2_zfmisc_1(X22,X23)) = k1_zfmisc_1(k2_zfmisc_1(X24,X25))) | ~v1_partfun1(sK5(k2_zfmisc_1(X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23))),X24)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3354,axiom,
% 5.55/1.12      ((~(![X18, X20, X19, X21] : ((v1_funct_2(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20,X21) | (k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relat_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~v1_partfun1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20))))) | (![X18, X20, X19, X21] : ((v1_funct_2(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20,X21) | (k2_relset_1(X18,X19,sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) = k2_relat_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))) | (k1_zfmisc_1(k2_zfmisc_1(X20,X21)) = k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~v1_partfun1(sK5(k2_zfmisc_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19))),X20)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3353,axiom,
% 5.55/1.12      ((~(![X5, X6] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5,X6) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5))))) | (![X5, X6] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5,X6) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3352,axiom,
% 5.55/1.12      ((~(![X5, X4] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4))))) | (![X5, X4] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4,X5) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))),X4)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3351,axiom,
% 5.55/1.12      ((~(![X9, X7, X8] : ((v1_funct_2(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8,k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)))) | r1_tarski(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X7) | ~v1_partfun1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8) | ~v1_funct_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7))) | (k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(X7)))))) | (![X9, X7, X8] : ((v1_funct_2(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8,k2_relat_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)))) | r1_tarski(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X7) | ~v1_partfun1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7)),X8) | ~v1_funct_1(sK5(k2_zfmisc_1(X8,X9),k1_zfmisc_1(X7))) | (k1_zfmisc_1(k2_zfmisc_1(X8,X9)) = k1_zfmisc_1(X7))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3350,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)))))) | (![X1, X0] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))) | (k1_xboole_0 = sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3349,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))) | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)))))) | (![X1, X0] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))) | v1_xboole_0(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3348,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3347,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X2,X3,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X0) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3346,axiom,
% 5.55/1.12      ((~(![X9, X11, X10, X12] : ((v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))) | v4_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))) | (![X9, X11, X10, X12] : ((v1_funct_2(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11,k2_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))))) | v4_relat_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X9) | ~v1_partfun1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3345,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (k1_xboole_0 = sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3344,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))) | (![X1, X0] : ((v1_funct_2(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,k2_relat_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) | ~v1_funct_1(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(sK5(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3343,axiom,
% 5.55/1.12      ((~(![X9, X7, X8] : ((v1_funct_2(sK5(k2_zfmisc_1(X7,X8),X9),X7,k2_relat_1(sK5(k2_zfmisc_1(X7,X8),X9))) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9) | ~v1_partfun1(sK5(k2_zfmisc_1(X7,X8),X9),X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X7,X8),X9)) | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9))))) | (![X9, X7, X8] : ((v1_funct_2(sK5(k2_zfmisc_1(X7,X8),X9),X7,k2_relat_1(sK5(k2_zfmisc_1(X7,X8),X9))) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = X9) | ~v1_partfun1(sK5(k2_zfmisc_1(X7,X8),X9),X7) | ~v1_funct_1(sK5(k2_zfmisc_1(X7,X8),X9)) | r2_hidden(sK5(k2_zfmisc_1(X7,X8),X9),X9)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3342,axiom,
% 5.55/1.12      ((~(![X9, X7, X8] : ((v1_funct_2(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,k2_relat_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))) | r1_tarski(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X9) | ~v1_partfun1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X9)))))) | (![X9, X7, X8] : ((v1_funct_2(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7,k2_relat_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))) | r1_tarski(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X9) | ~v1_partfun1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))),X7) | ~v1_funct_1(sK5(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))) | (k1_zfmisc_1(k2_zfmisc_1(X7,X8)) = k1_zfmisc_1(X9))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3341,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))))) | (![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relset_1(X0,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3340,axiom,
% 5.55/1.12      ((~(![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))) | (![X1, X3, X0, X2] : ((v1_funct_2(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2,k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | (k2_relset_1(X0,X1,sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))),X2) | ~v1_funct_1(sK5(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) | (k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3339,axiom,
% 5.55/1.12      ((~(![X9, X11, X10, X12] : ((v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,k2_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))) | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9) | ~v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))) | (![X9, X11, X10, X12] : ((v1_funct_2(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11,k2_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))))) | v4_relat_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X9) | ~v1_partfun1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X11) | ~v1_funct_1(sK5(k2_zfmisc_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) | (k1_zfmisc_1(k2_zfmisc_1(X11,X12)) = k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3338,axiom,
% 5.55/1.12      ((~(![X22, X21, X23, X24] : ((v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23,X24) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | ~v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) | (k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) = k2_relset_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23))))) | (![X22, X21, X23, X24] : ((v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23,X24) | (k1_zfmisc_1(k2_zfmisc_1(X21,X22)) = k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | ~v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) | (k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))) = k2_relset_1(X21,k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24)))),sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))))) | ~v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X23,X24))),X23)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3337,axiom,
% 5.55/1.12      ((~(![X20, X22, X19, X21] : ((v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19,X20) | (k2_relset_1(X21,X22,sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) = k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) | (k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19))))) | (![X20, X22, X19, X21] : ((v1_funct_2(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19,X20) | (k2_relset_1(X21,X22,sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) = k2_relat_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))))) | ~v1_funct_1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) | (k1_zfmisc_1(k2_zfmisc_1(X19,X20)) = k1_zfmisc_1(k2_zfmisc_1(X21,X22))) | ~v1_partfun1(sK5(k2_zfmisc_1(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20))),X19)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3336,negated_conjecture,
% 5.55/1.12      ((~~v2_struct_0(sK1)) | ~v2_struct_0(sK1))).
% 5.55/1.12  
% 5.55/1.12  tff(u3335,negated_conjecture,
% 5.55/1.12      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3334,axiom,
% 5.55/1.12      ((~(![X0] : ((~v2_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))))) | (![X0] : ((~v2_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3333,negated_conjecture,
% 5.55/1.12      ((~l1_struct_0(sK1)) | l1_struct_0(sK1))).
% 5.55/1.12  
% 5.55/1.12  tff(u3332,negated_conjecture,
% 5.55/1.12      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3331,axiom,
% 5.55/1.12      ((~(![X0] : ((l1_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))))) | (![X0] : ((l1_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3330,axiom,
% 5.55/1.12      ((~(![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))) | (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3329,negated_conjecture,
% 5.55/1.12      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 5.55/1.12  
% 5.55/1.12  tff(u3328,negated_conjecture,
% 5.55/1.12      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 5.55/1.12  
% 5.55/1.12  tff(u3327,axiom,
% 5.55/1.12      ((~(![X0] : ((l1_orders_2(sK4(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0))))) | (![X0] : ((l1_orders_2(sK4(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3326,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~m1_yellow_0(X1,X0) | (u1_orders_2(X1) = u1_orders_2(X0)) | ~m1_yellow_0(X0,X1) | ~l1_orders_2(X1))))) | (![X1, X0] : ((~m1_yellow_0(X1,X0) | (u1_orders_2(X1) = u1_orders_2(X0)) | ~m1_yellow_0(X0,X1) | ~l1_orders_2(X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3325,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~m1_yellow_0(X1,X0) | (u1_struct_0(X0) = u1_struct_0(X1)) | ~m1_yellow_0(X0,X1) | ~l1_orders_2(X1))))) | (![X1, X0] : ((~m1_yellow_0(X1,X0) | (u1_struct_0(X0) = u1_struct_0(X1)) | ~m1_yellow_0(X0,X1) | ~l1_orders_2(X1)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3324,axiom,
% 5.55/1.12      ((~(![X1, X0] : ((~m1_yellow_0(X1,X0) | l1_orders_2(X1) | ~l1_orders_2(X0))))) | (![X1, X0] : ((~m1_yellow_0(X1,X0) | l1_orders_2(X1) | ~l1_orders_2(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3323,axiom,
% 5.55/1.12      ((~(![X0] : ((~m1_yellow_0(X0,sK4(X0)) | (u1_orders_2(X0) = u1_orders_2(sK4(X0))) | ~l1_orders_2(sK4(X0)) | v2_struct_0(X0))))) | (![X0] : ((~m1_yellow_0(X0,sK4(X0)) | (u1_orders_2(X0) = u1_orders_2(sK4(X0))) | ~l1_orders_2(sK4(X0)) | v2_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3322,axiom,
% 5.55/1.12      ((~(![X0] : ((~m1_yellow_0(X0,sK4(X0)) | (u1_struct_0(X0) = u1_struct_0(sK4(X0))) | ~l1_orders_2(sK4(X0)) | v2_struct_0(X0))))) | (![X0] : ((~m1_yellow_0(X0,sK4(X0)) | (u1_struct_0(X0) = u1_struct_0(sK4(X0))) | ~l1_orders_2(sK4(X0)) | v2_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3321,negated_conjecture,
% 5.55/1.12      ((~(![X0] : ((~m1_yellow_0(sK0,X0) | ~m1_yellow_0(X0,sK0) | (u1_struct_0(X0) = k1_relat_1(sK2)) | ~l1_orders_2(X0))))) | (![X0] : ((~m1_yellow_0(sK0,X0) | ~m1_yellow_0(X0,sK0) | (u1_struct_0(X0) = k1_relat_1(sK2)) | ~l1_orders_2(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3320,axiom,
% 5.55/1.12      ((~(![X0] : ((m1_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))) | (![X0] : ((m1_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)))))).
% 5.55/1.12  
% 5.55/1.12  tff(u3319,axiom,
% 5.55/1.12      ((~(![X2] : ((m1_yellow_0(X2,X2) | ~l1_orders_2(X2))))) | (![X2] : ((m1_yellow_0(X2,X2) | ~l1_orders_2(X2)))))).
% 5.55/1.12  
% 5.55/1.12  % (17533)# SZS output end Saturation.
% 5.55/1.12  % (17533)------------------------------
% 5.55/1.12  % (17533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.55/1.12  % (17533)Termination reason: Satisfiable
% 5.55/1.12  
% 5.55/1.12  % (17533)Memory used [KB]: 8699
% 5.55/1.12  % (17533)Time elapsed: 0.260 s
% 5.55/1.12  % (17533)------------------------------
% 5.55/1.12  % (17533)------------------------------
% 5.55/1.12  % (17485)Success in time 0.749 s
%------------------------------------------------------------------------------
