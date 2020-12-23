%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BBCYJ4ygaP

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:55 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  344 ( 666 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X28: $i] :
      ( ( ( k3_relat_1 @ X28 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X28 ) @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X28: $i] :
      ( ( ( k3_relat_1 @ X28 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X28: $i] :
      ( ( ( k3_relat_1 @ X28 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k1_relat_1 @ X30 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X28: $i] :
      ( ( ( k3_relat_1 @ X28 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','36'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BBCYJ4ygaP
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:13:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.74/1.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.94  % Solved by: fo/fo7.sh
% 1.74/1.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.94  % done 4189 iterations in 1.474s
% 1.74/1.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.94  % SZS output start Refutation
% 1.74/1.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.94  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.74/1.94  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.74/1.94  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.74/1.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.74/1.94  thf(t31_relat_1, conjecture,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( v1_relat_1 @ A ) =>
% 1.74/1.94       ( ![B:$i]:
% 1.74/1.94         ( ( v1_relat_1 @ B ) =>
% 1.74/1.94           ( ( r1_tarski @ A @ B ) =>
% 1.74/1.94             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.74/1.94  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.94    (~( ![A:$i]:
% 1.74/1.94        ( ( v1_relat_1 @ A ) =>
% 1.74/1.94          ( ![B:$i]:
% 1.74/1.94            ( ( v1_relat_1 @ B ) =>
% 1.74/1.94              ( ( r1_tarski @ A @ B ) =>
% 1.74/1.94                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.74/1.94    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.74/1.94  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf(d6_relat_1, axiom,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( v1_relat_1 @ A ) =>
% 1.74/1.94       ( ( k3_relat_1 @ A ) =
% 1.74/1.94         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.74/1.94  thf('1', plain,
% 1.74/1.94      (![X28 : $i]:
% 1.74/1.94         (((k3_relat_1 @ X28)
% 1.74/1.94            = (k2_xboole_0 @ (k1_relat_1 @ X28) @ (k2_relat_1 @ X28)))
% 1.74/1.94          | ~ (v1_relat_1 @ X28))),
% 1.74/1.94      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.74/1.94  thf(commutativity_k2_xboole_0, axiom,
% 1.74/1.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.74/1.94  thf('2', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.74/1.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.74/1.94  thf('3', plain,
% 1.74/1.94      (![X28 : $i]:
% 1.74/1.94         (((k3_relat_1 @ X28)
% 1.74/1.94            = (k2_xboole_0 @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X28)))
% 1.74/1.94          | ~ (v1_relat_1 @ X28))),
% 1.74/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.74/1.94  thf('4', plain,
% 1.74/1.94      (![X28 : $i]:
% 1.74/1.94         (((k3_relat_1 @ X28)
% 1.74/1.94            = (k2_xboole_0 @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X28)))
% 1.74/1.94          | ~ (v1_relat_1 @ X28))),
% 1.74/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.74/1.94  thf('5', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.74/1.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.74/1.94  thf(t7_xboole_1, axiom,
% 1.74/1.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.74/1.94  thf('6', plain,
% 1.74/1.94      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.74/1.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.74/1.94  thf('7', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.74/1.94      inference('sup+', [status(thm)], ['5', '6'])).
% 1.74/1.94  thf('8', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.74/1.94          | ~ (v1_relat_1 @ X0))),
% 1.74/1.94      inference('sup+', [status(thm)], ['4', '7'])).
% 1.74/1.94  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf(t25_relat_1, axiom,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( v1_relat_1 @ A ) =>
% 1.74/1.94       ( ![B:$i]:
% 1.74/1.94         ( ( v1_relat_1 @ B ) =>
% 1.74/1.94           ( ( r1_tarski @ A @ B ) =>
% 1.74/1.94             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.74/1.94               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.74/1.94  thf('10', plain,
% 1.74/1.94      (![X29 : $i, X30 : $i]:
% 1.74/1.94         (~ (v1_relat_1 @ X29)
% 1.74/1.94          | (r1_tarski @ (k1_relat_1 @ X30) @ (k1_relat_1 @ X29))
% 1.74/1.94          | ~ (r1_tarski @ X30 @ X29)
% 1.74/1.94          | ~ (v1_relat_1 @ X30))),
% 1.74/1.94      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.74/1.94  thf('11', plain,
% 1.74/1.94      ((~ (v1_relat_1 @ sk_A)
% 1.74/1.94        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.74/1.94        | ~ (v1_relat_1 @ sk_B))),
% 1.74/1.94      inference('sup-', [status(thm)], ['9', '10'])).
% 1.74/1.94  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.74/1.94      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.74/1.94  thf(t1_xboole_1, axiom,
% 1.74/1.94    (![A:$i,B:$i,C:$i]:
% 1.74/1.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.74/1.94       ( r1_tarski @ A @ C ) ))).
% 1.74/1.94  thf('15', plain,
% 1.74/1.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.74/1.94         (~ (r1_tarski @ X7 @ X8)
% 1.74/1.94          | ~ (r1_tarski @ X8 @ X9)
% 1.74/1.94          | (r1_tarski @ X7 @ X9))),
% 1.74/1.94      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.74/1.94  thf('16', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.74/1.94          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.74/1.94      inference('sup-', [status(thm)], ['14', '15'])).
% 1.74/1.94  thf('17', plain,
% 1.74/1.94      ((~ (v1_relat_1 @ sk_B)
% 1.74/1.94        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['8', '16'])).
% 1.74/1.94  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.74/1.94      inference('demod', [status(thm)], ['17', '18'])).
% 1.74/1.94  thf('20', plain,
% 1.74/1.94      (![X28 : $i]:
% 1.74/1.94         (((k3_relat_1 @ X28)
% 1.74/1.94            = (k2_xboole_0 @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X28)))
% 1.74/1.94          | ~ (v1_relat_1 @ X28))),
% 1.74/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.74/1.94  thf('21', plain,
% 1.74/1.94      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.74/1.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.74/1.94  thf('22', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.74/1.94          | ~ (v1_relat_1 @ X0))),
% 1.74/1.94      inference('sup+', [status(thm)], ['20', '21'])).
% 1.74/1.94  thf('23', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('24', plain,
% 1.74/1.94      (![X29 : $i, X30 : $i]:
% 1.74/1.94         (~ (v1_relat_1 @ X29)
% 1.74/1.94          | (r1_tarski @ (k2_relat_1 @ X30) @ (k2_relat_1 @ X29))
% 1.74/1.94          | ~ (r1_tarski @ X30 @ X29)
% 1.74/1.94          | ~ (v1_relat_1 @ X30))),
% 1.74/1.94      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.74/1.94  thf('25', plain,
% 1.74/1.94      ((~ (v1_relat_1 @ sk_A)
% 1.74/1.94        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.74/1.94        | ~ (v1_relat_1 @ sk_B))),
% 1.74/1.94      inference('sup-', [status(thm)], ['23', '24'])).
% 1.74/1.94  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.74/1.94      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.74/1.94  thf('29', plain,
% 1.74/1.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.74/1.94         (~ (r1_tarski @ X7 @ X8)
% 1.74/1.94          | ~ (r1_tarski @ X8 @ X9)
% 1.74/1.94          | (r1_tarski @ X7 @ X9))),
% 1.74/1.94      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.74/1.94  thf('30', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.74/1.94          | ~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.74/1.94      inference('sup-', [status(thm)], ['28', '29'])).
% 1.74/1.94  thf('31', plain,
% 1.74/1.94      ((~ (v1_relat_1 @ sk_B)
% 1.74/1.94        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['22', '30'])).
% 1.74/1.94  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.74/1.94      inference('demod', [status(thm)], ['31', '32'])).
% 1.74/1.94  thf(t8_xboole_1, axiom,
% 1.74/1.94    (![A:$i,B:$i,C:$i]:
% 1.74/1.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.74/1.94       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.74/1.94  thf('34', plain,
% 1.74/1.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.74/1.94         (~ (r1_tarski @ X20 @ X21)
% 1.74/1.94          | ~ (r1_tarski @ X22 @ X21)
% 1.74/1.94          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 1.74/1.94      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.74/1.94  thf('35', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 1.74/1.94           (k3_relat_1 @ sk_B))
% 1.74/1.94          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['33', '34'])).
% 1.74/1.94  thf('36', plain,
% 1.74/1.94      ((r1_tarski @ 
% 1.74/1.94        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 1.74/1.94        (k3_relat_1 @ sk_B))),
% 1.74/1.94      inference('sup-', [status(thm)], ['19', '35'])).
% 1.74/1.94  thf('37', plain,
% 1.74/1.94      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.74/1.94        | ~ (v1_relat_1 @ sk_A))),
% 1.74/1.94      inference('sup+', [status(thm)], ['3', '36'])).
% 1.74/1.94  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('39', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.74/1.94      inference('demod', [status(thm)], ['37', '38'])).
% 1.74/1.94  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 1.74/1.94  
% 1.74/1.94  % SZS output end Refutation
% 1.74/1.94  
% 1.74/1.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
