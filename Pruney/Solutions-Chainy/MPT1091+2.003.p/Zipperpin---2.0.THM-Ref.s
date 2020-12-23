%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YHJ53YhTkm

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  92 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  382 ( 682 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t25_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
    <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_finset_1 @ A )
          & ! [B: $i] :
              ( ( r2_hidden @ B @ A )
             => ( v1_finset_1 @ B ) ) )
      <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(fc17_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( v1_finset_1 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( v1_finset_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc17_finset_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ ( k1_zfmisc_1 @ ( k3_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_finset_1 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_finset_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k3_tarski @ X0 ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ X16 )
      | ~ ( r2_hidden @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ! [X16: $i] :
        ( ( v1_finset_1 @ X16 )
        | ~ ( r2_hidden @ X16 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(l22_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
     => ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 )
      | ~ ( v1_finset_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('18',plain,
    ( ! [X16: $i] :
        ( ( v1_finset_1 @ X16 )
        | ~ ( r2_hidden @ X16 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( v1_finset_1 @ X16 )
        | ~ ( r2_hidden @ X16 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('19',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ ( sk_B @ sk_A ) ) )
   <= ! [X16: $i] :
        ( ( v1_finset_1 @ X16 )
        | ~ ( r2_hidden @ X16 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X13 ) )
      | ~ ( v1_finset_1 @ ( sk_B @ X13 ) )
      | ~ ( v1_finset_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('21',plain,
    ( ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v1_finset_1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( v1_finset_1 @ X16 )
        | ~ ( r2_hidden @ X16 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( ( v1_finset_1 @ sk_A )
      & ! [X16: $i] :
          ( ( v1_finset_1 @ X16 )
          | ~ ( r2_hidden @ X16 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('24',plain,
    ( ~ ! [X16: $i] :
          ( ( v1_finset_1 @ X16 )
          | ~ ( r2_hidden @ X16 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('26',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k3_tarski @ sk_A ) )
        | ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_finset_1 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_finset_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('37',plain,
    ( ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_finset_1 @ sk_B_1 )
   <= ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
   <= ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','13','15','24','25','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YHJ53YhTkm
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 57 iterations in 0.030s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t25_finset_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_finset_1 @ A ) & 
% 0.21/0.50         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.21/0.50       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v1_finset_1 @ A ) & 
% 0.21/0.50            ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.21/0.50          ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t25_finset_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.21/0.50        | ~ (v1_finset_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (~ ((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ sk_B_1)) | 
% 0.21/0.50       ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.21/0.50         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(fc17_finset_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X12 : $i]:
% 0.21/0.50         ((v1_finset_1 @ (k1_zfmisc_1 @ X12)) | ~ (v1_finset_1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc17_finset_1])).
% 0.21/0.50  thf(t100_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X11 : $i]: (r1_tarski @ X11 @ (k1_zfmisc_1 @ (k3_tarski @ X11)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.21/0.50  thf(t13_finset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         ((v1_finset_1 @ X14)
% 0.21/0.50          | ~ (r1_tarski @ X14 @ X15)
% 0.21/0.50          | ~ (v1_finset_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_finset_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.21/0.50          | (v1_finset_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_finset_1 @ (k3_tarski @ X0)) | (v1_finset_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.21/0.50        | (r2_hidden @ sk_B_1 @ sk_A)
% 0.21/0.50        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X16 : $i]:
% 0.21/0.50         ((v1_finset_1 @ (k3_tarski @ sk_A))
% 0.21/0.50          | (v1_finset_1 @ X16)
% 0.21/0.50          | ~ (r2_hidden @ X16 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A))) | 
% 0.21/0.50       ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['14'])).
% 0.21/0.50  thf('16', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(l22_finset_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_finset_1 @ A ) & 
% 0.21/0.50         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) =>
% 0.21/0.50       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X13 : $i]:
% 0.21/0.50         ((v1_finset_1 @ (k3_tarski @ X13))
% 0.21/0.50          | (r2_hidden @ (sk_B @ X13) @ X13)
% 0.21/0.50          | ~ (v1_finset_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A)))
% 0.21/0.50         <= ((![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['14'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (((~ (v1_finset_1 @ sk_A)
% 0.21/0.50         | (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.21/0.50         | (v1_finset_1 @ (sk_B @ sk_A))))
% 0.21/0.50         <= ((![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X13 : $i]:
% 0.21/0.50         ((v1_finset_1 @ (k3_tarski @ X13))
% 0.21/0.50          | ~ (v1_finset_1 @ (sk_B @ X13))
% 0.21/0.50          | ~ (v1_finset_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((((v1_finset_1 @ (k3_tarski @ sk_A)) | ~ (v1_finset_1 @ sk_A)))
% 0.21/0.50         <= ((![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A))))),
% 0.21/0.50      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.21/0.50         <= (((v1_finset_1 @ sk_A)) & 
% 0.21/0.50             (![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((~ (v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.21/0.50         <= (~ ((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (~ (![X16 : $i]: ((v1_finset_1 @ X16) | ~ (r2_hidden @ X16 @ sk_A))) | 
% 0.21/0.50       ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.21/0.50       ~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.21/0.50         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['10'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf(d4_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.50           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.50          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.50          | (r2_hidden @ X6 @ X7)
% 0.21/0.50          | ((X7) != (k3_tarski @ X5)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.21/0.50          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.50          | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ X0 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ X2)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k3_tarski @ sk_A))
% 0.21/0.50           | (r1_tarski @ sk_B_1 @ X0)))
% 0.21/0.50         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((((r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A))
% 0.21/0.50         | (r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A))))
% 0.21/0.50         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A)))
% 0.21/0.50         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         ((v1_finset_1 @ X14)
% 0.21/0.50          | ~ (r1_tarski @ X14 @ X15)
% 0.21/0.50          | ~ (v1_finset_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((~ (v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_B_1)))
% 0.21/0.50         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((v1_finset_1 @ sk_B_1))
% 0.21/0.50         <= (((v1_finset_1 @ (k3_tarski @ sk_A))) & 
% 0.21/0.50             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((~ (v1_finset_1 @ sk_B_1)) <= (~ ((v1_finset_1 @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.21/0.50       ~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ((v1_finset_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['1', '12', '13', '15', '24', '25', '40'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
