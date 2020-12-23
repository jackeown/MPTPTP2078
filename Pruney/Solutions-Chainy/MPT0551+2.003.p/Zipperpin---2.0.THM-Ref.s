%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IB8BqqruRN

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:24 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  366 ( 452 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t107_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ X4 @ X5 ) @ ( k7_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t107_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X10 @ X9 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k2_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k2_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t153_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
          = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t153_relat_1])).

thf('15',plain,(
    ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
     != ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
     != ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IB8BqqruRN
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:21:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 12 iterations in 0.013s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.18/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.18/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.46  thf(t148_relat_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ B ) =>
% 0.18/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.18/0.46  thf('0', plain,
% 0.18/0.46      (![X7 : $i, X8 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.18/0.46          | ~ (v1_relat_1 @ X7))),
% 0.18/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      (![X7 : $i, X8 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.18/0.46          | ~ (v1_relat_1 @ X7))),
% 0.18/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.18/0.46  thf(t107_relat_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ C ) =>
% 0.18/0.46       ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.18/0.46         ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.18/0.46         (((k7_relat_1 @ X4 @ (k2_xboole_0 @ X5 @ X6))
% 0.18/0.46            = (k2_xboole_0 @ (k7_relat_1 @ X4 @ X5) @ (k7_relat_1 @ X4 @ X6)))
% 0.18/0.46          | ~ (v1_relat_1 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t107_relat_1])).
% 0.18/0.46  thf(dt_k7_relat_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (![X2 : $i, X3 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X2) | (v1_relat_1 @ (k7_relat_1 @ X2 @ X3)))),
% 0.18/0.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (![X7 : $i, X8 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.18/0.46          | ~ (v1_relat_1 @ X7))),
% 0.18/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.18/0.46  thf(t26_relat_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ A ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( v1_relat_1 @ B ) =>
% 0.18/0.46           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.18/0.46             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      (![X9 : $i, X10 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X9)
% 0.18/0.46          | ((k2_relat_1 @ (k2_xboole_0 @ X10 @ X9))
% 0.18/0.46              = (k2_xboole_0 @ (k2_relat_1 @ X10) @ (k2_relat_1 @ X9)))
% 0.18/0.46          | ~ (v1_relat_1 @ X10))),
% 0.18/0.46      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.18/0.46  thf('6', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k2_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.18/0.46            = (k2_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X2)))
% 0.18/0.46          | ~ (v1_relat_1 @ X1)
% 0.18/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.18/0.46          | ~ (v1_relat_1 @ X2))),
% 0.18/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X1)
% 0.18/0.46          | ~ (v1_relat_1 @ X2)
% 0.18/0.46          | ~ (v1_relat_1 @ X1)
% 0.18/0.46          | ((k2_relat_1 @ (k2_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.18/0.46              = (k2_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X2))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k2_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.18/0.46            = (k2_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X2)))
% 0.18/0.46          | ~ (v1_relat_1 @ X2)
% 0.18/0.46          | ~ (v1_relat_1 @ X1))),
% 0.18/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.18/0.46            = (k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.18/0.46               (k2_relat_1 @ (k7_relat_1 @ X2 @ X0))))
% 0.18/0.46          | ~ (v1_relat_1 @ X2)
% 0.18/0.46          | ~ (v1_relat_1 @ X2)
% 0.18/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0)))),
% 0.18/0.46      inference('sup+', [status(thm)], ['2', '8'])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0))
% 0.18/0.46          | ~ (v1_relat_1 @ X2)
% 0.18/0.46          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.18/0.46              = (k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.18/0.46                 (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X2 : $i, X3 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X2) | (v1_relat_1 @ (k7_relat_1 @ X2 @ X3)))),
% 0.18/0.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.18/0.46            = (k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.18/0.46               (k2_relat_1 @ (k7_relat_1 @ X2 @ X0))))
% 0.18/0.46          | ~ (v1_relat_1 @ X2))),
% 0.18/0.46      inference('clc', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf('13', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_xboole_0 @ X2 @ X0)))
% 0.18/0.46            = (k2_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.18/0.46          | ~ (v1_relat_1 @ X1)
% 0.18/0.46          | ~ (v1_relat_1 @ X1))),
% 0.18/0.46      inference('sup+', [status(thm)], ['1', '12'])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X1)
% 0.18/0.46          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_xboole_0 @ X2 @ X0)))
% 0.18/0.46              = (k2_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.18/0.46  thf(t153_relat_1, conjecture,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ C ) =>
% 0.18/0.46       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.18/0.46         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.46        ( ( v1_relat_1 @ C ) =>
% 0.18/0.46          ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.18/0.46            ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t153_relat_1])).
% 0.18/0.46  thf('15', plain,
% 0.18/0.46      (((k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.18/0.46         != (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.18/0.46             (k9_relat_1 @ sk_C @ sk_B)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('16', plain,
% 0.18/0.46      ((((k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.18/0.46          != (k2_relat_1 @ (k7_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))))
% 0.18/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.18/0.46  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('18', plain,
% 0.18/0.46      (((k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.18/0.46         != (k2_relat_1 @ (k7_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.18/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.18/0.46  thf('19', plain,
% 0.18/0.46      ((((k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.18/0.46          != (k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))
% 0.18/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['0', '18'])).
% 0.18/0.46  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (((k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.18/0.46         != (k9_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.18/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.46  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
