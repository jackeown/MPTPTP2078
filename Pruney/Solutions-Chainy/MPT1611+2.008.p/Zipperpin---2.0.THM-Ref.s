%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UnVXWAjir4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:16 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 262 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 (1555 expanded)
%              Number of equality atoms :   53 ( 240 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X17 ) @ X17 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X17 ) )
        = ( k3_tarski @ X17 ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k9_setfam_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('22',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('24',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('25',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('26',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t13_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t13_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_setfam_1 @ ( k3_tarski @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('39',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('40',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('41',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','37','38','39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UnVXWAjir4
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 286 iterations in 0.245s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.47/0.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.47/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.70  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.70  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(t19_yellow_1, conjecture,
% 0.47/0.70    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.47/0.70  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t99_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.47/0.70  thf('1', plain, (![X15 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X15)) = (X15))),
% 0.47/0.70      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.47/0.70  thf(redefinition_k9_setfam_1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.70  thf('2', plain, (![X16 : $i]: ((k9_setfam_1 @ X16) = (k1_zfmisc_1 @ X16))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.47/0.70  thf('3', plain, (![X15 : $i]: ((k3_tarski @ (k9_setfam_1 @ X15)) = (X15))),
% 0.47/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf(t14_yellow_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.70       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.47/0.70         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X17 : $i]:
% 0.47/0.70         (~ (r2_hidden @ (k3_tarski @ X17) @ X17)
% 0.47/0.70          | ((k4_yellow_0 @ (k2_yellow_1 @ X17)) = (k3_tarski @ X17))
% 0.47/0.70          | (v1_xboole_0 @ X17))),
% 0.47/0.70      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.47/0.70          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.47/0.70          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.47/0.70              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.70  thf(t4_yellow_1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k2_yellow_1 @ (k9_setfam_1 @ X18)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.47/0.70  thf('7', plain, (![X15 : $i]: ((k3_tarski @ (k9_setfam_1 @ X15)) = (X15))),
% 0.47/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.47/0.70          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.47/0.70          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.47/0.70  thf(d10_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.70  thf('10', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.47/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.70  thf(d1_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.47/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X6 @ X7)
% 0.47/0.70          | (r2_hidden @ X6 @ X8)
% 0.47/0.70          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i]:
% 0.47/0.70         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.47/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.70  thf('13', plain, (![X16 : $i]: ((k9_setfam_1 @ X16) = (k1_zfmisc_1 @ X16))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i]:
% 0.47/0.70         ((r2_hidden @ X6 @ (k9_setfam_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '14'])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.47/0.70          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '15'])).
% 0.47/0.70  thf('17', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      ((((sk_A) != (sk_A)) | (v1_xboole_0 @ (k9_setfam_1 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.70  thf('19', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.47/0.70      inference('simplify', [status(thm)], ['18'])).
% 0.47/0.70  thf('20', plain, (![X15 : $i]: ((k3_tarski @ (k9_setfam_1 @ X15)) = (X15))),
% 0.47/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf(l13_xboole_0, axiom,
% 0.47/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.70  thf('22', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (![X0 : $i]: (((k3_tarski @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['21', '22'])).
% 0.47/0.70  thf(t1_zfmisc_1, axiom,
% 0.47/0.70    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.47/0.70  thf('24', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.47/0.70  thf('25', plain, (![X16 : $i]: ((k9_setfam_1 @ X16) = (k1_zfmisc_1 @ X16))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.47/0.70  thf('26', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf(t1_boole, axiom,
% 0.47/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.70  thf('28', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.47/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((k2_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['27', '28'])).
% 0.47/0.70  thf(t13_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.47/0.70         ( k1_tarski @ A ) ) =>
% 0.47/0.70       ( ( A ) = ( B ) ) ))).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      (![X11 : $i, X12 : $i]:
% 0.47/0.70         (((X12) = (X11))
% 0.47/0.70          | ((k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.47/0.70              != (k1_tarski @ X12)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t13_zfmisc_1])).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.47/0.70          | ~ (v1_xboole_0 @ (k1_tarski @ X1))
% 0.47/0.70          | ((X0) = (X1)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((X0) = (X1)) | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ (k9_setfam_1 @ k1_xboole_0))
% 0.47/0.70          | ((X0) = (k1_xboole_0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['26', '32'])).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ (k9_setfam_1 @ (k3_tarski @ X0)))
% 0.47/0.70          | ~ (v1_xboole_0 @ X0)
% 0.47/0.70          | ((X1) = (k1_xboole_0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['23', '33'])).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.47/0.70          | ((X1) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_xboole_0 @ (k9_setfam_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['20', '34'])).
% 0.47/0.70  thf('36', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k9_setfam_1 @ X0)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['35'])).
% 0.47/0.70  thf('37', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['19', '36'])).
% 0.47/0.70  thf('38', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['19', '36'])).
% 0.47/0.70  thf('39', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['19', '36'])).
% 0.47/0.70  thf('40', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['19', '36'])).
% 0.47/0.70  thf('41', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['0', '37', '38', '39', '40'])).
% 0.47/0.70  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
