%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Edib1oVfO

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:46 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 132 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 ( 989 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_D_1 @ X11 @ X9 ) ) @ X9 )
      | ( X10
       != ( k1_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('18',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_D_1 @ X11 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ ( k11_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['13','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k11_relat_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k1_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','28','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['30','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Edib1oVfO
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:41 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 143 iterations in 0.099s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(l13_xboole_0, axiom,
% 0.38/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.56  thf(t205_relat_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.38/0.56         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( v1_relat_1 @ B ) =>
% 0.38/0.56          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.38/0.56            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.38/0.56         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (((X0) != (k1_xboole_0))
% 0.38/0.56           | ~ (v1_xboole_0 @ X0)
% 0.38/0.56           | ~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.38/0.56         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))
% 0.38/0.56         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.38/0.56         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.56  thf('8', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.38/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.56  thf(l24_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X5 : $i, X6 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ (k1_tarski @ X5) @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.38/0.56  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.38/0.56         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect+', [status(thm)], ['6', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.38/0.56       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['3'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.38/0.56        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['14'])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.38/0.56      inference('split', [status(esa)], ['3'])).
% 0.38/0.56  thf(d4_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X11 @ X10)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X11 @ (sk_D_1 @ X11 @ X9)) @ X9)
% 0.38/0.56          | ((X10) != (k1_relat_1 @ X9)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X9 : $i, X11 : $i]:
% 0.38/0.56         ((r2_hidden @ (k4_tarski @ X11 @ (sk_D_1 @ X11 @ X9)) @ X9)
% 0.38/0.56          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X9)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '18'])).
% 0.38/0.56  thf(t204_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ C ) =>
% 0.38/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.56         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.56         (~ (r2_hidden @ (k4_tarski @ X16 @ X14) @ X15)
% 0.38/0.56          | (r2_hidden @ X14 @ (k11_relat_1 @ X15 @ X16))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (((~ (v1_relat_1 @ sk_B_1)
% 0.38/0.56         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.38/0.56            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.38/0.56             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '25'])).
% 0.38/0.56  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.38/0.56       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['13', '28'])).
% 0.38/0.56  thf('30', plain, (~ (v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['12', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X14 @ (k11_relat_1 @ X15 @ X16))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X16 @ X14) @ X15)
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k11_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.38/0.56             X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.56         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.38/0.56          | (r2_hidden @ X7 @ X10)
% 0.38/0.56          | ((X10) != (k1_relat_1 @ X9)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         ((r2_hidden @ X7 @ (k1_relat_1 @ X9))
% 0.38/0.56          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.38/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k11_relat_1 @ X0 @ X1))
% 0.38/0.56          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['33', '35'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.38/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.38/0.56      inference('split', [status(esa)], ['14'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.38/0.56       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('split', [status(esa)], ['14'])).
% 0.38/0.56  thf('39', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['13', '28', '38'])).
% 0.38/0.56  thf('40', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['36', '40'])).
% 0.38/0.56  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('43', plain, ((v1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('44', plain, ($false), inference('demod', [status(thm)], ['30', '43'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
