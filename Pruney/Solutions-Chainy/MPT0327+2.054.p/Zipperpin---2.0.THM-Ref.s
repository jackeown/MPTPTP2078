%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QmHiZu9WsS

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:57 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  488 ( 902 expanded)
%              Number of equality atoms :   46 (  79 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('6',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('8',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('9',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 != X45 )
      | ~ ( r2_hidden @ X43 @ ( k4_xboole_0 @ X44 @ ( k1_tarski @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('10',plain,(
    ! [X44: $i,X45: $i] :
      ~ ( r2_hidden @ X45 @ ( k4_xboole_0 @ X44 @ ( k1_tarski @ X45 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('19',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
     != sk_B )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('32',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','41'])).

thf('43',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('44',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['11','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QmHiZu9WsS
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.97  % Solved by: fo/fo7.sh
% 0.79/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.97  % done 1130 iterations in 0.520s
% 0.79/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.97  % SZS output start Refutation
% 0.79/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.79/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.79/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.79/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.97  thf(t140_zfmisc_1, conjecture,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r2_hidden @ A @ B ) =>
% 0.79/0.97       ( ( k2_xboole_0 @
% 0.79/0.97           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.79/0.97         ( B ) ) ))).
% 0.79/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.97    (~( ![A:$i,B:$i]:
% 0.79/0.97        ( ( r2_hidden @ A @ B ) =>
% 0.79/0.97          ( ( k2_xboole_0 @
% 0.79/0.97              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.79/0.97            ( B ) ) ) )),
% 0.79/0.97    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.79/0.97  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf(l1_zfmisc_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.79/0.97  thf('1', plain,
% 0.79/0.97      (![X35 : $i, X37 : $i]:
% 0.79/0.97         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.79/0.97      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.79/0.97  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.79/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/0.97  thf(l32_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.79/0.97  thf('3', plain,
% 0.79/0.97      (![X6 : $i, X8 : $i]:
% 0.79/0.97         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.79/0.97      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.79/0.97  thf('4', plain,
% 0.79/0.97      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.79/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.79/0.97  thf(d6_xboole_0, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( k5_xboole_0 @ A @ B ) =
% 0.79/0.97       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.79/0.97  thf('5', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         ((k5_xboole_0 @ X0 @ X1)
% 0.79/0.97           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.79/0.97  thf('6', plain,
% 0.79/0.97      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.79/0.97         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.79/0.97            k1_xboole_0))),
% 0.79/0.97      inference('sup+', [status(thm)], ['4', '5'])).
% 0.79/0.97  thf(t1_boole, axiom,
% 0.79/0.97    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/0.97  thf('7', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.79/0.97      inference('cnf', [status(esa)], [t1_boole])).
% 0.79/0.97  thf('8', plain,
% 0.79/0.97      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.79/0.97         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['6', '7'])).
% 0.79/0.97  thf(t64_zfmisc_1, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i]:
% 0.79/0.97     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.79/0.97       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.79/0.97  thf('9', plain,
% 0.79/0.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.79/0.97         (((X43) != (X45))
% 0.79/0.97          | ~ (r2_hidden @ X43 @ (k4_xboole_0 @ X44 @ (k1_tarski @ X45))))),
% 0.79/0.97      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.79/0.97  thf('10', plain,
% 0.79/0.97      (![X44 : $i, X45 : $i]:
% 0.79/0.97         ~ (r2_hidden @ X45 @ (k4_xboole_0 @ X44 @ (k1_tarski @ X45)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['9'])).
% 0.79/0.97  thf('11', plain,
% 0.79/0.97      (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['8', '10'])).
% 0.79/0.97  thf(l27_zfmisc_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.79/0.97  thf('12', plain,
% 0.79/0.97      (![X38 : $i, X39 : $i]:
% 0.79/0.97         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 0.79/0.97      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.79/0.97  thf(t83_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/0.97  thf('13', plain,
% 0.79/0.97      (![X18 : $i, X19 : $i]:
% 0.79/0.97         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.79/0.97      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.79/0.97  thf('14', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         ((r2_hidden @ X1 @ X0)
% 0.79/0.97          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.79/0.97  thf(t98_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.79/0.97  thf('15', plain,
% 0.79/0.97      (![X23 : $i, X24 : $i]:
% 0.79/0.97         ((k2_xboole_0 @ X23 @ X24)
% 0.79/0.97           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.79/0.97      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.79/0.97  thf('16', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.79/0.97            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.79/0.97          | (r2_hidden @ X0 @ X1))),
% 0.79/0.97      inference('sup+', [status(thm)], ['14', '15'])).
% 0.79/0.97  thf('17', plain,
% 0.79/0.97      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.79/0.97         (k1_tarski @ sk_A)) != (sk_B))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('18', plain,
% 0.79/0.97      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.79/0.97         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['6', '7'])).
% 0.79/0.97  thf('19', plain,
% 0.79/0.97      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.79/0.97         (k1_tarski @ sk_A)) != (sk_B))),
% 0.79/0.97      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.97  thf('20', plain,
% 0.79/0.97      ((((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.79/0.97          (k1_tarski @ sk_A)) != (sk_B))
% 0.79/0.97        | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.79/0.97      inference('sup-', [status(thm)], ['16', '19'])).
% 0.79/0.97  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.79/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/0.97  thf(t28_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/0.97  thf('22', plain,
% 0.79/0.97      (![X14 : $i, X15 : $i]:
% 0.79/0.97         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.79/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/0.97  thf('23', plain,
% 0.79/0.97      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.79/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/0.97  thf(t94_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( k2_xboole_0 @ A @ B ) =
% 0.79/0.97       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.79/0.97  thf('24', plain,
% 0.79/0.97      (![X21 : $i, X22 : $i]:
% 0.79/0.97         ((k2_xboole_0 @ X21 @ X22)
% 0.79/0.97           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.79/0.97              (k3_xboole_0 @ X21 @ X22)))),
% 0.79/0.97      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.79/0.97  thf('25', plain,
% 0.79/0.97      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.79/0.97         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.79/0.97            (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('sup+', [status(thm)], ['23', '24'])).
% 0.79/0.97  thf('26', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.79/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/0.97  thf(t12_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.79/0.97  thf('27', plain,
% 0.79/0.97      (![X11 : $i, X12 : $i]:
% 0.79/0.97         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.79/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.79/0.97  thf('28', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.79/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.79/0.97  thf('29', plain,
% 0.79/0.97      (((sk_B)
% 0.79/0.97         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.79/0.97            (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['25', '28'])).
% 0.79/0.97  thf('30', plain,
% 0.79/0.97      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.79/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.79/0.97  thf('31', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         ((k5_xboole_0 @ X0 @ X1)
% 0.79/0.97           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.79/0.97  thf('32', plain,
% 0.79/0.97      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.79/0.97         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.79/0.97            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.79/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.79/0.97  thf('33', plain,
% 0.79/0.97      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.79/0.97         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['6', '7'])).
% 0.79/0.97  thf(d10_xboole_0, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/0.97  thf('34', plain,
% 0.79/0.97      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.79/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.97  thf('35', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.79/0.97      inference('simplify', [status(thm)], ['34'])).
% 0.79/0.97  thf('36', plain,
% 0.79/0.97      (![X6 : $i, X8 : $i]:
% 0.79/0.97         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.79/0.97      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.79/0.97  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.79/0.97  thf(t36_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.79/0.97  thf('38', plain,
% 0.79/0.97      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.79/0.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.79/0.97  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.79/0.97      inference('sup+', [status(thm)], ['37', '38'])).
% 0.79/0.97  thf('40', plain,
% 0.79/0.97      (![X11 : $i, X12 : $i]:
% 0.79/0.97         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.79/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.79/0.97  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.79/0.97      inference('sup-', [status(thm)], ['39', '40'])).
% 0.79/0.97  thf('42', plain,
% 0.79/0.97      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.79/0.97         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['32', '33', '41'])).
% 0.79/0.97  thf('43', plain,
% 0.79/0.97      (((sk_B)
% 0.79/0.97         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.79/0.97            (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('demod', [status(thm)], ['29', '42'])).
% 0.79/0.97  thf('44', plain,
% 0.79/0.97      ((((sk_B) != (sk_B))
% 0.79/0.97        | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.79/0.97      inference('demod', [status(thm)], ['20', '43'])).
% 0.79/0.97  thf('45', plain,
% 0.79/0.97      ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['44'])).
% 0.79/0.97  thf('46', plain, ($false), inference('demod', [status(thm)], ['11', '45'])).
% 0.79/0.97  
% 0.79/0.97  % SZS output end Refutation
% 0.79/0.97  
% 0.79/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
