%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xNwUvsNywl

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 119 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  360 ( 860 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf(t62_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_1])).

thf('2',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('9',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('15',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('30',plain,(
    ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38','39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xNwUvsNywl
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 21 iterations in 0.014s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.47  thf(fc5_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.20/0.47         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X3 : $i]:
% 0.20/0.47         ((v1_relat_1 @ (k4_relat_1 @ X3))
% 0.20/0.47          | ~ (v2_funct_1 @ X3)
% 0.20/0.47          | ~ (v1_funct_1 @ X3)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X3 : $i]:
% 0.20/0.47         ((v1_funct_1 @ (k4_relat_1 @ X3))
% 0.20/0.47          | ~ (v2_funct_1 @ X3)
% 0.20/0.47          | ~ (v1_funct_1 @ X3)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.20/0.47  thf(t62_funct_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47          ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t62_funct_1])).
% 0.20/0.47  thf('2', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d9_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X0)
% 0.20/0.47          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.47        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.47  thf(t61_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) =>
% 0.20/0.47         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.20/0.47             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.47           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.20/0.47             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X7 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X7)
% 0.20/0.47          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 0.20/0.47              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.20/0.47          | ~ (v1_funct_1 @ X7)
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.20/0.47          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.47        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.20/0.47         = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.20/0.47  thf(t48_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.20/0.47               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.47             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | (v2_funct_1 @ X4)
% 0.20/0.47          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.20/0.47          | ~ (v2_funct_1 @ (k5_relat_1 @ X4 @ X5))
% 0.20/0.47          | ~ (v1_funct_1 @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.47        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 0.20/0.47        | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(fc4_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.47  thf('16', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.47  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.47  thf(t55_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) =>
% 0.20/0.47         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.47           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X6 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X6)
% 0.20/0.47          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 0.20/0.47          | ~ (v1_funct_1 @ X6)
% 0.20/0.47          | ~ (v1_relat_1 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.47        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.20/0.47        | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16', '17', '18', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.47  thf('30', plain, (~ (v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['27', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.47        | ~ (v2_funct_1 @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '31'])).
% 0.20/0.47  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('36', plain, (~ (v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '36'])).
% 0.20/0.47  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
