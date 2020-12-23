%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MGJWAte0TC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 120 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  363 ( 880 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf('0',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('10',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X4 @ X3 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','32'])).

thf('34',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['7','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MGJWAte0TC
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 27 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(t62_funct_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47          ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t62_funct_1])).
% 0.21/0.47  thf('0', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d9_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X1 : $i]:
% 0.21/0.47         (~ (v2_funct_1 @ X1)
% 0.21/0.47          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.47        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.21/0.47        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf('7', plain, (~ (v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '6'])).
% 0.21/0.47  thf('8', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf(t61_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v2_funct_1 @ A ) =>
% 0.21/0.47         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.47             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.47           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.47             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X5 : $i]:
% 0.21/0.47         (~ (v2_funct_1 @ X5)
% 0.21/0.47          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.21/0.47              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.21/0.47          | ~ (v1_funct_1 @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.21/0.47          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.47        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.21/0.47         = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.47  thf('15', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf(dt_k2_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.47         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X2 : $i]:
% 0.21/0.47         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.21/0.47          | ~ (v1_funct_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.47  thf(t37_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.47         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.47  thf(t53_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( ?[B:$i]:
% 0.21/0.47           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.47             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.21/0.47         ( v2_funct_1 @ A ) ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X3)
% 0.21/0.47          | ~ (v1_funct_1 @ X3)
% 0.21/0.47          | ((k5_relat_1 @ X4 @ X3) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.21/0.47          | (v2_funct_1 @ X4)
% 0.21/0.47          | ~ (v1_funct_1 @ X4)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k5_relat_1 @ (k4_relat_1 @ X0) @ X1)
% 0.21/0.47            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.21/0.47          | (v2_funct_1 @ (k4_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_funct_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47          | ((k5_relat_1 @ (k4_relat_1 @ sk_A) @ X0)
% 0.21/0.47              != (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.47  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47          | ((k5_relat_1 @ (k4_relat_1 @ sk_A) @ X0)
% 0.21/0.47              != (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X2 : $i]:
% 0.21/0.47         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.21/0.47          | ~ (v1_funct_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47          | ((k5_relat_1 @ (k4_relat_1 @ sk_A) @ X0)
% 0.21/0.47              != (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['26', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.21/0.47          != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.21/0.47        | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.21/0.47        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.47        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '33'])).
% 0.21/0.47  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((((k6_relat_1 @ (k2_relat_1 @ sk_A))
% 0.21/0.47          != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.21/0.47        | (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.47  thf('38', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.47  thf('39', plain, ($false), inference('demod', [status(thm)], ['7', '38'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
