%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G1h1SjFSKu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:00 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   66 (  91 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  394 ( 674 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( ( k3_relat_1 @ X14 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X14: $i] :
      ( ( ( k3_relat_1 @ X14 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i] :
      ( ( ( k3_relat_1 @ X14 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G1h1SjFSKu
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 21:01:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.51/1.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.75  % Solved by: fo/fo7.sh
% 1.51/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.75  % done 2894 iterations in 1.289s
% 1.51/1.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.75  % SZS output start Refutation
% 1.51/1.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.75  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.51/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.75  thf(t31_relat_1, conjecture,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( v1_relat_1 @ A ) =>
% 1.51/1.75       ( ![B:$i]:
% 1.51/1.75         ( ( v1_relat_1 @ B ) =>
% 1.51/1.75           ( ( r1_tarski @ A @ B ) =>
% 1.51/1.75             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.51/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.75    (~( ![A:$i]:
% 1.51/1.75        ( ( v1_relat_1 @ A ) =>
% 1.51/1.75          ( ![B:$i]:
% 1.51/1.75            ( ( v1_relat_1 @ B ) =>
% 1.51/1.75              ( ( r1_tarski @ A @ B ) =>
% 1.51/1.75                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.51/1.75    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.51/1.75  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(d6_relat_1, axiom,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( v1_relat_1 @ A ) =>
% 1.51/1.75       ( ( k3_relat_1 @ A ) =
% 1.51/1.75         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.51/1.75  thf('1', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         (((k3_relat_1 @ X14)
% 1.51/1.75            = (k2_xboole_0 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.51/1.75  thf('2', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         (((k3_relat_1 @ X14)
% 1.51/1.75            = (k2_xboole_0 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.51/1.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.51/1.75  thf('3', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.51/1.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.51/1.75  thf(t9_xboole_1, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( r1_tarski @ A @ B ) =>
% 1.51/1.75       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.51/1.75  thf('4', plain,
% 1.51/1.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.51/1.75         (~ (r1_tarski @ X11 @ X12)
% 1.51/1.75          | (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ (k2_xboole_0 @ X12 @ X13)))),
% 1.51/1.75      inference('cnf', [status(esa)], [t9_xboole_1])).
% 1.51/1.75  thf('5', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]:
% 1.51/1.75         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 1.51/1.75          (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.75      inference('sup-', [status(thm)], ['3', '4'])).
% 1.51/1.75  thf('6', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.51/1.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.51/1.75  thf(t12_xboole_1, axiom,
% 1.51/1.75    (![A:$i,B:$i]:
% 1.51/1.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.51/1.75  thf('7', plain,
% 1.51/1.75      (![X3 : $i, X4 : $i]:
% 1.51/1.75         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.51/1.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.75  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['6', '7'])).
% 1.51/1.75  thf('9', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.75      inference('demod', [status(thm)], ['5', '8'])).
% 1.51/1.75  thf('10', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('sup+', [status(thm)], ['2', '9'])).
% 1.51/1.75  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf(t25_relat_1, axiom,
% 1.51/1.75    (![A:$i]:
% 1.51/1.75     ( ( v1_relat_1 @ A ) =>
% 1.51/1.75       ( ![B:$i]:
% 1.51/1.75         ( ( v1_relat_1 @ B ) =>
% 1.51/1.75           ( ( r1_tarski @ A @ B ) =>
% 1.51/1.75             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.51/1.75               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.51/1.75  thf('12', plain,
% 1.51/1.75      (![X15 : $i, X16 : $i]:
% 1.51/1.75         (~ (v1_relat_1 @ X15)
% 1.51/1.75          | (r1_tarski @ (k2_relat_1 @ X16) @ (k2_relat_1 @ X15))
% 1.51/1.75          | ~ (r1_tarski @ X16 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X16))),
% 1.51/1.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.51/1.75  thf('13', plain,
% 1.51/1.75      ((~ (v1_relat_1 @ sk_A)
% 1.51/1.75        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.51/1.75        | ~ (v1_relat_1 @ sk_B))),
% 1.51/1.75      inference('sup-', [status(thm)], ['11', '12'])).
% 1.51/1.75  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.51/1.75      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.51/1.75  thf('17', plain,
% 1.51/1.75      (![X3 : $i, X4 : $i]:
% 1.51/1.75         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.51/1.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.75  thf('18', plain,
% 1.51/1.75      (((k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.51/1.75         = (k2_relat_1 @ sk_B))),
% 1.51/1.75      inference('sup-', [status(thm)], ['16', '17'])).
% 1.51/1.75  thf(t11_xboole_1, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.51/1.75  thf('19', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.75         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 1.51/1.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.51/1.75  thf('20', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.51/1.75          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['18', '19'])).
% 1.51/1.75  thf('21', plain,
% 1.51/1.75      ((~ (v1_relat_1 @ sk_B)
% 1.51/1.75        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['10', '20'])).
% 1.51/1.75  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.51/1.75      inference('demod', [status(thm)], ['21', '22'])).
% 1.51/1.75  thf('24', plain,
% 1.51/1.75      (![X14 : $i]:
% 1.51/1.75         (((k3_relat_1 @ X14)
% 1.51/1.75            = (k2_xboole_0 @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X14)))
% 1.51/1.75          | ~ (v1_relat_1 @ X14))),
% 1.51/1.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.51/1.75  thf(t7_xboole_1, axiom,
% 1.51/1.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.75  thf('25', plain,
% 1.51/1.75      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.51/1.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.51/1.75  thf('26', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.51/1.75          | ~ (v1_relat_1 @ X0))),
% 1.51/1.75      inference('sup+', [status(thm)], ['24', '25'])).
% 1.51/1.75  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('28', plain,
% 1.51/1.75      (![X15 : $i, X16 : $i]:
% 1.51/1.75         (~ (v1_relat_1 @ X15)
% 1.51/1.75          | (r1_tarski @ (k1_relat_1 @ X16) @ (k1_relat_1 @ X15))
% 1.51/1.75          | ~ (r1_tarski @ X16 @ X15)
% 1.51/1.75          | ~ (v1_relat_1 @ X16))),
% 1.51/1.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.51/1.75  thf('29', plain,
% 1.51/1.75      ((~ (v1_relat_1 @ sk_A)
% 1.51/1.75        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.51/1.75        | ~ (v1_relat_1 @ sk_B))),
% 1.51/1.75      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.75  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.51/1.75      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.51/1.75  thf('33', plain,
% 1.51/1.75      (![X3 : $i, X4 : $i]:
% 1.51/1.75         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.51/1.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.75  thf('34', plain,
% 1.51/1.75      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.51/1.75         = (k1_relat_1 @ sk_B))),
% 1.51/1.75      inference('sup-', [status(thm)], ['32', '33'])).
% 1.51/1.75  thf('35', plain,
% 1.51/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.75         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 1.51/1.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.51/1.75  thf('36', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.51/1.75          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 1.51/1.75      inference('sup-', [status(thm)], ['34', '35'])).
% 1.51/1.75  thf('37', plain,
% 1.51/1.75      ((~ (v1_relat_1 @ sk_B)
% 1.51/1.75        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['26', '36'])).
% 1.51/1.75  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('39', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.51/1.75      inference('demod', [status(thm)], ['37', '38'])).
% 1.51/1.75  thf(t8_xboole_1, axiom,
% 1.51/1.75    (![A:$i,B:$i,C:$i]:
% 1.51/1.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.51/1.75       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.51/1.75  thf('40', plain,
% 1.51/1.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.75         (~ (r1_tarski @ X8 @ X9)
% 1.51/1.75          | ~ (r1_tarski @ X10 @ X9)
% 1.51/1.75          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.51/1.75      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.51/1.75  thf('41', plain,
% 1.51/1.75      (![X0 : $i]:
% 1.51/1.75         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.51/1.75           (k3_relat_1 @ sk_B))
% 1.51/1.75          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.51/1.75      inference('sup-', [status(thm)], ['39', '40'])).
% 1.51/1.75  thf('42', plain,
% 1.51/1.75      ((r1_tarski @ 
% 1.51/1.75        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.51/1.75        (k3_relat_1 @ sk_B))),
% 1.51/1.75      inference('sup-', [status(thm)], ['23', '41'])).
% 1.51/1.75  thf('43', plain,
% 1.51/1.75      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.51/1.75        | ~ (v1_relat_1 @ sk_A))),
% 1.51/1.75      inference('sup+', [status(thm)], ['1', '42'])).
% 1.51/1.75  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 1.51/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.75  thf('45', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.51/1.75      inference('demod', [status(thm)], ['43', '44'])).
% 1.51/1.75  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 1.51/1.75  
% 1.51/1.75  % SZS output end Refutation
% 1.51/1.75  
% 1.51/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
