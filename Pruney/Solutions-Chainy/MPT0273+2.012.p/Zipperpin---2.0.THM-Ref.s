%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MJfm9KA5cu

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 234 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  612 (3118 expanded)
%              Number of equality atoms :   77 ( 364 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t70_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ( ( r2_hidden @ B @ C )
            | ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X30 )
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('7',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_A != sk_B )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = X31 )
      | ( r2_hidden @ X31 @ X30 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X30 )
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_B @ sk_C )
      | ( sk_A = sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_B @ sk_C )
      & ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_A != sk_B )
      & ~ ( r2_hidden @ sk_B @ sk_C )
      & ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( ~ ( r2_hidden @ sk_A @ sk_C )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( sk_A = sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X32 )
        = ( k1_tarski @ X29 ) )
      | ( X29 != X31 )
      | ( r2_hidden @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X31 @ X31 ) @ X32 )
        = ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','16','17','9','26'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A = sk_B ) ),
    inference(simpl_trail,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != sk_B ),
    inference(demod,[status(thm)],['31','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('45',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['15','16','17','9','26','43','44'])).

thf('46',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['13','45'])).

thf('47',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X32 )
        = ( k1_tarski @ X29 ) )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ sk_C )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('50',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','16','17','9','26'])).

thf('51',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['11','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MJfm9KA5cu
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 66 iterations in 0.026s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(t70_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.48         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48          ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.48            ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t70_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.21/0.48        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48            = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.21/0.48        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.48        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48            != (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))
% 0.21/0.48         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(l38_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.48         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X29 @ X30)
% 0.21/0.48          | ((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X30) != (k1_tarski @ X29)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.48         | ~ (r2_hidden @ sk_A @ sk_C)))
% 0.21/0.48         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ sk_C))
% 0.21/0.48         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.48       ~
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.48  thf('10', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.21/0.48  thf('11', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((sk_A) = (sk_B))
% 0.21/0.48        | (r2_hidden @ sk_B @ sk_C)
% 0.21/0.48        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48            = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_A) != (sk_B))
% 0.21/0.48        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.48        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48            != (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.48       ~
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.48       ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('split', [status(esa)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))
% 0.21/0.48         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.48         (((X29) = (X31))
% 0.21/0.48          | (r2_hidden @ X31 @ X30)
% 0.21/0.48          | ((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X30) != (k1_tarski @ X29)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.48         | (r2_hidden @ sk_B @ sk_C)
% 0.21/0.48         | ((sk_A) = (sk_B))))
% 0.21/0.48         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_C)))
% 0.21/0.48         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((sk_A) = (sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_B @ sk_C)) & 
% 0.21/0.48             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['14'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((sk_B) != (sk_B)))
% 0.21/0.48         <= (~ (((sk_A) = (sk_B))) & 
% 0.21/0.48             ~ ((r2_hidden @ sk_B @ sk_C)) & 
% 0.21/0.48             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.21/0.48       ~
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))) | 
% 0.21/0.48       (((sk_A) = (sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf('27', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['12'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_C))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ sk_C)) & (((sk_A) = (sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.21/0.48  thf('31', plain, ((~ (r2_hidden @ sk_B @ sk_C)) <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X32) = (k1_tarski @ X29))
% 0.21/0.48          | ((X29) != (X31))
% 0.21/0.48          | (r2_hidden @ X29 @ X32))),
% 0.21/0.48      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X31 : $i, X32 : $i]:
% 0.21/0.48         ((r2_hidden @ X31 @ X32)
% 0.21/0.48          | ((k4_xboole_0 @ (k2_tarski @ X31 @ X31) @ X32) = (k1_tarski @ X31)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('34', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['12'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_B) @ sk_C) != (k1_tarski @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))) & 
% 0.21/0.48             (((sk_A) = (sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['12'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_B) @ sk_C) != (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))) & 
% 0.21/0.48             (((sk_A) = (sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['15', '16', '17', '9', '26'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_B) @ sk_C) != (k1_tarski @ sk_B)))
% 0.21/0.48         <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_C)))
% 0.21/0.48         <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '40'])).
% 0.21/0.48  thf('42', plain, (((r2_hidden @ sk_B @ sk_C)) <= ((((sk_A) = (sk_B))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.48  thf('43', plain, (~ (((sk_A) = (sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_C)) | (((sk_A) = (sk_B))) | 
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['12'])).
% 0.21/0.48  thf('45', plain, (((r2_hidden @ sk_B @ sk_C))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)],
% 0.21/0.48                ['15', '16', '17', '9', '26', '43', '44'])).
% 0.21/0.48  thf('46', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['13', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X32) = (k1_tarski @ X29))
% 0.21/0.48          | ~ (r2_hidden @ X31 @ X32)
% 0.21/0.48          | (r2_hidden @ X29 @ X32))),
% 0.21/0.48      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ sk_C)
% 0.21/0.48          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ sk_C) = (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.48                = (k1_tarski @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['15', '16', '17', '9', '26'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.48  thf('53', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.48  thf('54', plain, ($false), inference('demod', [status(thm)], ['11', '53'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
