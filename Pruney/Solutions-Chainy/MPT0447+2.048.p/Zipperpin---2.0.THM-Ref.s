%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bm8RBXedN9

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:59 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  375 ( 655 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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

thf('3',plain,(
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

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bm8RBXedN9
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:40:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.21/2.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.21/2.47  % Solved by: fo/fo7.sh
% 2.21/2.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.47  % done 2421 iterations in 2.013s
% 2.21/2.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.21/2.47  % SZS output start Refutation
% 2.21/2.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.21/2.47  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.21/2.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.21/2.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.21/2.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.21/2.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.21/2.47  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.21/2.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.21/2.47  thf(t31_relat_1, conjecture,
% 2.21/2.47    (![A:$i]:
% 2.21/2.47     ( ( v1_relat_1 @ A ) =>
% 2.21/2.47       ( ![B:$i]:
% 2.21/2.47         ( ( v1_relat_1 @ B ) =>
% 2.21/2.47           ( ( r1_tarski @ A @ B ) =>
% 2.21/2.47             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.21/2.47  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.47    (~( ![A:$i]:
% 2.21/2.47        ( ( v1_relat_1 @ A ) =>
% 2.21/2.47          ( ![B:$i]:
% 2.21/2.47            ( ( v1_relat_1 @ B ) =>
% 2.21/2.47              ( ( r1_tarski @ A @ B ) =>
% 2.21/2.47                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 2.21/2.47    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 2.21/2.47  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf(d6_relat_1, axiom,
% 2.21/2.47    (![A:$i]:
% 2.21/2.47     ( ( v1_relat_1 @ A ) =>
% 2.21/2.47       ( ( k3_relat_1 @ A ) =
% 2.21/2.47         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.21/2.47  thf('1', plain,
% 2.21/2.47      (![X12 : $i]:
% 2.21/2.47         (((k3_relat_1 @ X12)
% 2.21/2.47            = (k2_xboole_0 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 2.21/2.47          | ~ (v1_relat_1 @ X12))),
% 2.21/2.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.21/2.47  thf('2', plain,
% 2.21/2.47      (![X12 : $i]:
% 2.21/2.47         (((k3_relat_1 @ X12)
% 2.21/2.47            = (k2_xboole_0 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 2.21/2.47          | ~ (v1_relat_1 @ X12))),
% 2.21/2.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.21/2.47  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf(t25_relat_1, axiom,
% 2.21/2.47    (![A:$i]:
% 2.21/2.47     ( ( v1_relat_1 @ A ) =>
% 2.21/2.47       ( ![B:$i]:
% 2.21/2.47         ( ( v1_relat_1 @ B ) =>
% 2.21/2.47           ( ( r1_tarski @ A @ B ) =>
% 2.21/2.47             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 2.21/2.47               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 2.21/2.47  thf('4', plain,
% 2.21/2.47      (![X13 : $i, X14 : $i]:
% 2.21/2.47         (~ (v1_relat_1 @ X13)
% 2.21/2.47          | (r1_tarski @ (k2_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 2.21/2.47          | ~ (r1_tarski @ X14 @ X13)
% 2.21/2.47          | ~ (v1_relat_1 @ X14))),
% 2.21/2.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.21/2.47  thf('5', plain,
% 2.21/2.47      ((~ (v1_relat_1 @ sk_A)
% 2.21/2.47        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_B))),
% 2.21/2.47      inference('sup-', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 2.21/2.47  thf(t10_xboole_1, axiom,
% 2.21/2.47    (![A:$i,B:$i,C:$i]:
% 2.21/2.47     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.21/2.47  thf('9', plain,
% 2.21/2.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.21/2.47         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 2.21/2.47      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.21/2.47  thf('10', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 2.21/2.47          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['8', '9'])).
% 2.21/2.47  thf('11', plain,
% 2.21/2.47      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['2', '10'])).
% 2.21/2.47  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['11', '12'])).
% 2.21/2.47  thf(d3_tarski, axiom,
% 2.21/2.47    (![A:$i,B:$i]:
% 2.21/2.47     ( ( r1_tarski @ A @ B ) <=>
% 2.21/2.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.21/2.47  thf('14', plain,
% 2.21/2.47      (![X1 : $i, X3 : $i]:
% 2.21/2.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.47  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('16', plain,
% 2.21/2.47      (![X13 : $i, X14 : $i]:
% 2.21/2.47         (~ (v1_relat_1 @ X13)
% 2.21/2.47          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 2.21/2.47          | ~ (r1_tarski @ X14 @ X13)
% 2.21/2.47          | ~ (v1_relat_1 @ X14))),
% 2.21/2.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.21/2.47  thf('17', plain,
% 2.21/2.47      ((~ (v1_relat_1 @ sk_A)
% 2.21/2.47        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_B))),
% 2.21/2.47      inference('sup-', [status(thm)], ['15', '16'])).
% 2.21/2.47  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.21/2.47  thf('21', plain,
% 2.21/2.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.47         (~ (r2_hidden @ X0 @ X1)
% 2.21/2.47          | (r2_hidden @ X0 @ X2)
% 2.21/2.47          | ~ (r1_tarski @ X1 @ X2))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.47  thf('22', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 2.21/2.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_A)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['20', '21'])).
% 2.21/2.47  thf('23', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 2.21/2.47          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 2.21/2.47             (k1_relat_1 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['14', '22'])).
% 2.21/2.47  thf('24', plain,
% 2.21/2.47      (![X12 : $i]:
% 2.21/2.47         (((k3_relat_1 @ X12)
% 2.21/2.47            = (k2_xboole_0 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 2.21/2.47          | ~ (v1_relat_1 @ X12))),
% 2.21/2.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.21/2.47  thf(t7_xboole_1, axiom,
% 2.21/2.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.21/2.47  thf('25', plain,
% 2.21/2.47      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 2.21/2.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.21/2.47  thf('26', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.21/2.47          | ~ (v1_relat_1 @ X0))),
% 2.21/2.47      inference('sup+', [status(thm)], ['24', '25'])).
% 2.21/2.47  thf('27', plain,
% 2.21/2.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.47         (~ (r2_hidden @ X0 @ X1)
% 2.21/2.47          | (r2_hidden @ X0 @ X2)
% 2.21/2.47          | ~ (r1_tarski @ X1 @ X2))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.47  thf('28', plain,
% 2.21/2.47      (![X0 : $i, X1 : $i]:
% 2.21/2.47         (~ (v1_relat_1 @ X0)
% 2.21/2.47          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 2.21/2.47          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['26', '27'])).
% 2.21/2.47  thf('29', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 2.21/2.47          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 2.21/2.47             (k3_relat_1 @ sk_B))
% 2.21/2.47          | ~ (v1_relat_1 @ sk_B))),
% 2.21/2.47      inference('sup-', [status(thm)], ['23', '28'])).
% 2.21/2.47  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('31', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 2.21/2.47          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 2.21/2.47             (k3_relat_1 @ sk_B)))),
% 2.21/2.47      inference('demod', [status(thm)], ['29', '30'])).
% 2.21/2.47  thf('32', plain,
% 2.21/2.47      (![X1 : $i, X3 : $i]:
% 2.21/2.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.21/2.47  thf('33', plain,
% 2.21/2.47      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 2.21/2.47        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['31', '32'])).
% 2.21/2.47  thf('34', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.21/2.47      inference('simplify', [status(thm)], ['33'])).
% 2.21/2.47  thf(t8_xboole_1, axiom,
% 2.21/2.47    (![A:$i,B:$i,C:$i]:
% 2.21/2.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.21/2.47       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.21/2.47  thf('35', plain,
% 2.21/2.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.21/2.47         (~ (r1_tarski @ X9 @ X10)
% 2.21/2.47          | ~ (r1_tarski @ X11 @ X10)
% 2.21/2.47          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 2.21/2.47      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.21/2.47  thf('36', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 2.21/2.47           (k3_relat_1 @ sk_B))
% 2.21/2.47          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['34', '35'])).
% 2.21/2.47  thf('37', plain,
% 2.21/2.47      ((r1_tarski @ 
% 2.21/2.47        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 2.21/2.47        (k3_relat_1 @ sk_B))),
% 2.21/2.47      inference('sup-', [status(thm)], ['13', '36'])).
% 2.21/2.47  thf('38', plain,
% 2.21/2.47      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['1', '37'])).
% 2.21/2.47  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('40', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['38', '39'])).
% 2.21/2.47  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 2.21/2.47  
% 2.21/2.47  % SZS output end Refutation
% 2.21/2.47  
% 2.21/2.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
