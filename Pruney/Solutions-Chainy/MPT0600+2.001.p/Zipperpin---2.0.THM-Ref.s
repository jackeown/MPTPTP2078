%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XSvyY6OnP6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  515 ( 854 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t204_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t204_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X11 ) @ X7 )
      | ~ ( r2_hidden @ X12 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X11 ) @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('35',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( sk_D_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','18','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XSvyY6OnP6
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 41 iterations in 0.034s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(t204_relat_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ C ) =>
% 0.20/0.49          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49            ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t204_relat_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.49       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(d16_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf(d13_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i,C:$i]:
% 0.20/0.49         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.49           ( ![D:$i]:
% 0.20/0.49             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49               ( ?[E:$i]:
% 0.20/0.49                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.49                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (((X9) != (k9_relat_1 @ X7 @ X6))
% 0.20/0.49          | (r2_hidden @ X11 @ X9)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X12 @ X11) @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X12 @ X6)
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X12 @ X6)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X12 @ X11) @ X7)
% 0.20/0.49          | (r2_hidden @ X11 @ (k9_relat_1 @ X7 @ X6)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C_1 @ X0))
% 0.20/0.49           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.49           | ~ (v1_relat_1 @ sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.49  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C_1 @ X0))
% 0.20/0.49           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '12'])).
% 0.20/0.49  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.49       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.49  thf(t143_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.49         ( ?[D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.49             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X18 @ X16 @ X17) @ X17) @ X18)
% 0.20/0.49          | ~ (v1_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r2_hidden @ 
% 0.20/0.49           (k4_tarski @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49         | (r2_hidden @ 
% 0.20/0.49            (k4_tarski @ (sk_D_1 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.20/0.49            sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '23'])).
% 0.20/0.49  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['5'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.20/0.49          | (r2_hidden @ (sk_D_1 @ X18 @ X16 @ X17) @ X16)
% 0.20/0.49          | ~ (v1_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ 
% 0.20/0.49             (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49         | (r2_hidden @ (sk_D_1 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.20/0.49            (k1_tarski @ sk_A))))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '30'])).
% 0.20/0.49  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.20/0.49         (k1_tarski @ sk_A)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]:
% 0.20/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((((sk_D_1 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B) = (sk_A)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.49         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C_1 @ sk_A))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '17', '18', '39'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
