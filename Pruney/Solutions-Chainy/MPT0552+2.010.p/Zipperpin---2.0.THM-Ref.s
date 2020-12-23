%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ia7W4z1Kly

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:25 EST 2020

% Result     : Theorem 7.06s
% Output     : Refutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :   39 (  57 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  326 ( 533 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X23 )
        = ( k7_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ia7W4z1Kly
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.06/7.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.06/7.23  % Solved by: fo/fo7.sh
% 7.06/7.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.06/7.23  % done 6226 iterations in 6.775s
% 7.06/7.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.06/7.23  % SZS output start Refutation
% 7.06/7.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.06/7.23  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 7.06/7.23  thf(sk_C_type, type, sk_C: $i).
% 7.06/7.23  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.06/7.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.06/7.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.06/7.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.06/7.23  thf(sk_A_type, type, sk_A: $i).
% 7.06/7.23  thf(sk_B_type, type, sk_B: $i).
% 7.06/7.23  thf(commutativity_k3_xboole_0, axiom,
% 7.06/7.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.06/7.23  thf('0', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.06/7.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.06/7.23  thf(t100_relat_1, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( v1_relat_1 @ C ) =>
% 7.06/7.23       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 7.06/7.23         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 7.06/7.23  thf('1', plain,
% 7.06/7.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.06/7.23         (((k7_relat_1 @ (k7_relat_1 @ X21 @ X22) @ X23)
% 7.06/7.23            = (k7_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23)))
% 7.06/7.23          | ~ (v1_relat_1 @ X21))),
% 7.06/7.23      inference('cnf', [status(esa)], [t100_relat_1])).
% 7.06/7.23  thf(t148_relat_1, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( v1_relat_1 @ B ) =>
% 7.06/7.23       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 7.06/7.23  thf('2', plain,
% 7.06/7.23      (![X27 : $i, X28 : $i]:
% 7.06/7.23         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 7.06/7.23          | ~ (v1_relat_1 @ X27))),
% 7.06/7.23      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.06/7.23  thf('3', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.06/7.23            = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 7.06/7.23          | ~ (v1_relat_1 @ X2)
% 7.06/7.23          | ~ (v1_relat_1 @ X2))),
% 7.06/7.23      inference('sup+', [status(thm)], ['1', '2'])).
% 7.06/7.23  thf('4', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X2)
% 7.06/7.23          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.06/7.23              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 7.06/7.23      inference('simplify', [status(thm)], ['3'])).
% 7.06/7.23  thf('5', plain,
% 7.06/7.23      (![X27 : $i, X28 : $i]:
% 7.06/7.23         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 7.06/7.23          | ~ (v1_relat_1 @ X27))),
% 7.06/7.23      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.06/7.23  thf(t99_relat_1, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( v1_relat_1 @ B ) =>
% 7.06/7.23       ( r1_tarski @
% 7.06/7.23         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 7.06/7.23  thf('6', plain,
% 7.06/7.23      (![X31 : $i, X32 : $i]:
% 7.06/7.23         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X31 @ X32)) @ 
% 7.06/7.23           (k2_relat_1 @ X31))
% 7.06/7.23          | ~ (v1_relat_1 @ X31))),
% 7.06/7.23      inference('cnf', [status(esa)], [t99_relat_1])).
% 7.06/7.23  thf('7', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((r1_tarski @ 
% 7.06/7.23           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 7.06/7.23           (k9_relat_1 @ X1 @ X0))
% 7.06/7.23          | ~ (v1_relat_1 @ X1)
% 7.06/7.23          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.06/7.23      inference('sup+', [status(thm)], ['5', '6'])).
% 7.06/7.23  thf(dt_k7_relat_1, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 7.06/7.23  thf('8', plain,
% 7.06/7.23      (![X19 : $i, X20 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 7.06/7.23      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.06/7.23  thf('9', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X1)
% 7.06/7.23          | (r1_tarski @ 
% 7.06/7.23             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 7.06/7.23             (k9_relat_1 @ X1 @ X0)))),
% 7.06/7.23      inference('clc', [status(thm)], ['7', '8'])).
% 7.06/7.23  thf('10', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.06/7.23           (k9_relat_1 @ X2 @ X1))
% 7.06/7.23          | ~ (v1_relat_1 @ X2)
% 7.06/7.23          | ~ (v1_relat_1 @ X2))),
% 7.06/7.23      inference('sup+', [status(thm)], ['4', '9'])).
% 7.06/7.23  thf('11', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X2)
% 7.06/7.23          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.06/7.23             (k9_relat_1 @ X2 @ X1)))),
% 7.06/7.23      inference('simplify', [status(thm)], ['10'])).
% 7.06/7.23  thf('12', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.06/7.23           (k9_relat_1 @ X2 @ X0))
% 7.06/7.23          | ~ (v1_relat_1 @ X2))),
% 7.06/7.23      inference('sup+', [status(thm)], ['0', '11'])).
% 7.06/7.23  thf('13', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X2)
% 7.06/7.23          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.06/7.23             (k9_relat_1 @ X2 @ X1)))),
% 7.06/7.23      inference('simplify', [status(thm)], ['10'])).
% 7.06/7.23  thf(t19_xboole_1, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 7.06/7.23       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.06/7.23  thf('14', plain,
% 7.06/7.23      (![X4 : $i, X5 : $i, X6 : $i]:
% 7.06/7.23         (~ (r1_tarski @ X4 @ X5)
% 7.06/7.23          | ~ (r1_tarski @ X4 @ X6)
% 7.06/7.23          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.06/7.23      inference('cnf', [status(esa)], [t19_xboole_1])).
% 7.06/7.23  thf('15', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X1)
% 7.06/7.23          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 7.06/7.23             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 7.06/7.23          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 7.06/7.23      inference('sup-', [status(thm)], ['13', '14'])).
% 7.06/7.23  thf('16', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         (~ (v1_relat_1 @ X1)
% 7.06/7.23          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 7.06/7.23             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 7.06/7.23          | ~ (v1_relat_1 @ X1))),
% 7.06/7.23      inference('sup-', [status(thm)], ['12', '15'])).
% 7.06/7.23  thf('17', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 7.06/7.23           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 7.06/7.23          | ~ (v1_relat_1 @ X1))),
% 7.06/7.23      inference('simplify', [status(thm)], ['16'])).
% 7.06/7.23  thf(t154_relat_1, conjecture,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( v1_relat_1 @ C ) =>
% 7.06/7.23       ( r1_tarski @
% 7.06/7.23         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.06/7.23         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 7.06/7.23  thf(zf_stmt_0, negated_conjecture,
% 7.06/7.23    (~( ![A:$i,B:$i,C:$i]:
% 7.06/7.23        ( ( v1_relat_1 @ C ) =>
% 7.06/7.23          ( r1_tarski @
% 7.06/7.23            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.06/7.23            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 7.06/7.23    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 7.06/7.23  thf('18', plain,
% 7.06/7.23      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 7.06/7.23          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 7.06/7.23           (k9_relat_1 @ sk_C @ sk_B)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('19', plain, (~ (v1_relat_1 @ sk_C)),
% 7.06/7.23      inference('sup-', [status(thm)], ['17', '18'])).
% 7.06/7.23  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('21', plain, ($false), inference('demod', [status(thm)], ['19', '20'])).
% 7.06/7.23  
% 7.06/7.23  % SZS output end Refutation
% 7.06/7.23  
% 7.06/7.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
