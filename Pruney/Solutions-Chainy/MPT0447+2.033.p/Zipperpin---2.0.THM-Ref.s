%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h1QdQN3Vzj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  349 ( 672 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('36',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h1QdQN3Vzj
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 131 iterations in 0.075s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.53  thf(t31_relat_1, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( v1_relat_1 @ B ) =>
% 0.19/0.53           ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( v1_relat_1 @ A ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( v1_relat_1 @ B ) =>
% 0.19/0.53              ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 0.19/0.53  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d6_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ( k3_relat_1 @ A ) =
% 0.19/0.53         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X12 : $i]:
% 0.19/0.53         (((k3_relat_1 @ X12)
% 0.19/0.53            = (k2_xboole_0 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.19/0.53          | ~ (v1_relat_1 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X12 : $i]:
% 0.19/0.53         (((k3_relat_1 @ X12)
% 0.19/0.53            = (k2_xboole_0 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.19/0.53          | ~ (v1_relat_1 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.19/0.53  thf(commutativity_k2_tarski, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.53  thf(l51_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X10 : $i, X11 : $i]:
% 0.19/0.53         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.19/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X10 : $i, X11 : $i]:
% 0.19/0.53         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.19/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t25_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( v1_relat_1 @ B ) =>
% 0.19/0.53           ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.53               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X13)
% 0.19/0.53          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.19/0.53          | ~ (r1_tarski @ X14 @ X13)
% 0.19/0.53          | ~ (v1_relat_1 @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.53        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.19/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.19/0.53  thf(t10_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.19/0.53          (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.19/0.53          (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['7', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.19/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['2', '16'])).
% 0.19/0.53  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X12 : $i]:
% 0.19/0.53         (((k3_relat_1 @ X12)
% 0.19/0.53            = (k2_xboole_0 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.19/0.53          | ~ (v1_relat_1 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.19/0.53  thf('21', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X13)
% 0.19/0.53          | (r1_tarski @ (k2_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.19/0.53          | ~ (r1_tarski @ X14 @ X13)
% 0.19/0.53          | ~ (v1_relat_1 @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.53        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.19/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.53  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 0.19/0.53          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.19/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.53      inference('sup+', [status(thm)], ['20', '28'])).
% 0.19/0.53  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.53  thf(t8_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.19/0.53       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         (~ (r1_tarski @ X3 @ X4)
% 0.19/0.53          | ~ (r1_tarski @ X5 @ X4)
% 0.19/0.53          | (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.19/0.53      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 0.19/0.53           (k3_relat_1 @ sk_B))
% 0.19/0.53          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      ((r1_tarski @ 
% 0.19/0.53        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 0.19/0.53        (k3_relat_1 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['19', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      ((r1_tarski @ 
% 0.19/0.53        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 0.19/0.53        (k3_relat_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.19/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['1', '36'])).
% 0.19/0.53  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('39', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.53  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
