%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8RNeOZAPK6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:48 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 114 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  381 ( 913 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8
        = ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X8 @ X5 ) @ ( sk_D @ X8 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X8 @ X5 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k11_relat_1 @ X11 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

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

thf('12',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ ( k11_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['15','27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['13','29'])).

thf('31',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('35',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['15','27'])).

thf('36',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8RNeOZAPK6
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:35:33 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.17/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.46  % Solved by: fo/fo7.sh
% 0.17/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.46  % done 39 iterations in 0.027s
% 0.17/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.46  % SZS output start Refutation
% 0.17/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.17/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.17/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.17/0.46  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.17/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.17/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.17/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.17/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.17/0.46  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.17/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.17/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.17/0.46  thf(d4_relat_1, axiom,
% 0.17/0.46    (![A:$i,B:$i]:
% 0.17/0.46     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.17/0.46       ( ![C:$i]:
% 0.17/0.46         ( ( r2_hidden @ C @ B ) <=>
% 0.17/0.46           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.17/0.46  thf('0', plain,
% 0.17/0.46      (![X5 : $i, X8 : $i]:
% 0.17/0.46         (((X8) = (k1_relat_1 @ X5))
% 0.17/0.46          | (r2_hidden @ (k4_tarski @ (sk_C @ X8 @ X5) @ (sk_D @ X8 @ X5)) @ X5)
% 0.17/0.46          | (r2_hidden @ (sk_C @ X8 @ X5) @ X8))),
% 0.17/0.46      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.17/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.17/0.46  thf('1', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.17/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.17/0.46  thf(l24_zfmisc_1, axiom,
% 0.17/0.46    (![A:$i,B:$i]:
% 0.17/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.17/0.46  thf('2', plain,
% 0.17/0.46      (![X1 : $i, X2 : $i]:
% 0.17/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X1) @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.17/0.46      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.17/0.46  thf('3', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.17/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.46  thf('4', plain,
% 0.17/0.46      (![X0 : $i]:
% 0.17/0.46         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.17/0.46          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.17/0.46  thf(t60_relat_1, axiom,
% 0.17/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.17/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.17/0.46  thf('5', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.17/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.17/0.46  thf('6', plain,
% 0.17/0.46      (![X0 : $i]:
% 0.17/0.46         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.17/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.17/0.46  thf(t204_relat_1, axiom,
% 0.17/0.46    (![A:$i,B:$i,C:$i]:
% 0.17/0.46     ( ( v1_relat_1 @ C ) =>
% 0.17/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.17/0.46         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.17/0.46  thf('7', plain,
% 0.17/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.46         (~ (r2_hidden @ X10 @ (k11_relat_1 @ X11 @ X12))
% 0.17/0.46          | (r2_hidden @ (k4_tarski @ X12 @ X10) @ X11)
% 0.17/0.46          | ~ (v1_relat_1 @ X11))),
% 0.17/0.46      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.17/0.46  thf('8', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]:
% 0.17/0.46         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.17/0.46          | ~ (v1_relat_1 @ X1)
% 0.17/0.46          | (r2_hidden @ 
% 0.17/0.46             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 0.17/0.46             X1))),
% 0.17/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.17/0.46  thf('9', plain,
% 0.17/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.17/0.46         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.17/0.46          | (r2_hidden @ X3 @ X6)
% 0.17/0.46          | ((X6) != (k1_relat_1 @ X5)))),
% 0.17/0.46      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.17/0.46  thf('10', plain,
% 0.17/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.17/0.46         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.17/0.46          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.17/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.17/0.46  thf('11', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]:
% 0.17/0.46         (~ (v1_relat_1 @ X0)
% 0.17/0.46          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.17/0.46          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['8', '10'])).
% 0.17/0.46  thf(t205_relat_1, conjecture,
% 0.17/0.46    (![A:$i,B:$i]:
% 0.17/0.46     ( ( v1_relat_1 @ B ) =>
% 0.17/0.46       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.17/0.46         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.17/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.46    (~( ![A:$i,B:$i]:
% 0.17/0.46        ( ( v1_relat_1 @ B ) =>
% 0.17/0.46          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.17/0.46            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.17/0.46    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.17/0.46  thf('12', plain,
% 0.17/0.46      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.17/0.46        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('13', plain,
% 0.17/0.46      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.17/0.46         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.17/0.46      inference('split', [status(esa)], ['12'])).
% 0.17/0.46  thf('14', plain,
% 0.17/0.46      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.17/0.46        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('15', plain,
% 0.17/0.46      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.17/0.46       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.17/0.46      inference('split', [status(esa)], ['14'])).
% 0.17/0.46  thf('16', plain,
% 0.17/0.46      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.17/0.46         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.17/0.46      inference('split', [status(esa)], ['12'])).
% 0.17/0.46  thf('17', plain,
% 0.17/0.46      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.17/0.46         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.17/0.46      inference('split', [status(esa)], ['14'])).
% 0.17/0.46  thf('18', plain,
% 0.17/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.17/0.46         (~ (r2_hidden @ X7 @ X6)
% 0.17/0.46          | (r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.17/0.46          | ((X6) != (k1_relat_1 @ X5)))),
% 0.17/0.46      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.17/0.46  thf('19', plain,
% 0.17/0.46      (![X5 : $i, X7 : $i]:
% 0.17/0.46         ((r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.17/0.46          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X5)))),
% 0.17/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.17/0.46  thf('20', plain,
% 0.17/0.46      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.17/0.46         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.17/0.46      inference('sup-', [status(thm)], ['17', '19'])).
% 0.17/0.46  thf('21', plain,
% 0.17/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.46         (~ (r2_hidden @ (k4_tarski @ X12 @ X10) @ X11)
% 0.17/0.46          | (r2_hidden @ X10 @ (k11_relat_1 @ X11 @ X12))
% 0.17/0.46          | ~ (v1_relat_1 @ X11))),
% 0.17/0.46      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.17/0.46  thf('22', plain,
% 0.17/0.46      (((~ (v1_relat_1 @ sk_B)
% 0.17/0.46         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.17/0.46         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.17/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.17/0.46  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('24', plain,
% 0.17/0.46      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.17/0.46         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.17/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.17/0.46  thf('25', plain,
% 0.17/0.46      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.17/0.46         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.17/0.46             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.17/0.46      inference('sup+', [status(thm)], ['16', '24'])).
% 0.17/0.46  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.17/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.46  thf('27', plain,
% 0.17/0.46      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.17/0.46       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.17/0.46  thf('28', plain,
% 0.17/0.46      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.17/0.46       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.17/0.46      inference('split', [status(esa)], ['12'])).
% 0.17/0.46  thf('29', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.17/0.46      inference('sat_resolution*', [status(thm)], ['15', '27', '28'])).
% 0.17/0.46  thf('30', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.17/0.46      inference('simpl_trail', [status(thm)], ['13', '29'])).
% 0.17/0.46  thf('31', plain,
% 0.17/0.46      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.17/0.46      inference('sup-', [status(thm)], ['11', '30'])).
% 0.17/0.46  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('33', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.17/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.17/0.46  thf('34', plain,
% 0.17/0.46      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.17/0.46         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.17/0.46      inference('split', [status(esa)], ['14'])).
% 0.17/0.46  thf('35', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.17/0.46      inference('sat_resolution*', [status(thm)], ['15', '27'])).
% 0.17/0.46  thf('36', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.17/0.46      inference('simpl_trail', [status(thm)], ['34', '35'])).
% 0.17/0.46  thf('37', plain, ($false),
% 0.17/0.46      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 0.17/0.46  
% 0.17/0.46  % SZS output end Refutation
% 0.17/0.46  
% 0.17/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
