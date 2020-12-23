%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ru8IN0n0vQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:56 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 106 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 (1017 expanded)
%              Number of equality atoms :   50 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) )
        = X19 )
      | ( r2_hidden @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 != X15 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X25 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ( X13
        = ( k4_xboole_0 @ X13 @ ( k2_tarski @ X12 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( ( k4_xboole_0 @ X19 @ ( k1_tarski @ X18 ) )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('25',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('31',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['20','31'])).

thf('33',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('35',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('37',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('38',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['29','37'])).

thf('39',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ru8IN0n0vQ
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 400 iterations in 0.196s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(t65_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.46/0.65       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X19 @ (k1_tarski @ X20)) = (X19))
% 0.46/0.65          | (r2_hidden @ X20 @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.65  thf(t20_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.65         ( k1_tarski @ A ) ) <=>
% 0.46/0.65       ( ( A ) != ( B ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i]:
% 0.46/0.65         (((X16) != (X15))
% 0.46/0.65          | ((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X15))
% 0.46/0.65              != (k1_tarski @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.46/0.65           != (k1_tarski @ X15))),
% 0.46/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.46/0.65          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.65  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.65  thf(t18_mcart_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( r2_hidden @
% 0.46/0.65         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.46/0.65       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.46/0.65         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65        ( ( r2_hidden @
% 0.46/0.65            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.46/0.65          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.46/0.65            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ 
% 0.46/0.65        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t10_mcart_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.46/0.65       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.46/0.65         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         ((r2_hidden @ (k2_mcart_1 @ X25) @ X27)
% 0.46/0.65          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X26 @ X27)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf(t144_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.46/0.65          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.65         ((r2_hidden @ X12 @ X13)
% 0.46/0.65          | (r2_hidden @ X14 @ X13)
% 0.46/0.65          | ((X13) = (k4_xboole_0 @ X13 @ (k2_tarski @ X12 @ X14))))),
% 0.46/0.65      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.46/0.65  thf(d5_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.65          | ~ (r2_hidden @ X4 @ X2)
% 0.46/0.65          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.65          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X3 @ X0)
% 0.46/0.65          | (r2_hidden @ X1 @ X0)
% 0.46/0.65          | (r2_hidden @ X2 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ sk_C @ X0)
% 0.46/0.65          | (r2_hidden @ sk_D_1 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.46/0.65        | (r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.46/0.65            = (k1_tarski @ X16))
% 0.46/0.65          | ((X16) = (X17)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X18 @ X19)
% 0.46/0.65          | ((k4_xboole_0 @ X19 @ (k1_tarski @ X18)) != (X19)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.46/0.65          | ((X0) = (X1))
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.46/0.65        | ((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.46/0.65         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.46/0.65      inference('split', [status(esa)], ['19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ 
% 0.46/0.65        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         ((r2_hidden @ (k1_mcart_1 @ X25) @ X26)
% 0.46/0.65          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X26 @ X27)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.65  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.65  thf('25', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.46/0.65         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.46/0.65      inference('split', [status(esa)], ['26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '27'])).
% 0.46/0.65  thf('29', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) | 
% 0.46/0.65       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['19'])).
% 0.46/0.65  thf('31', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('32', plain, (((k2_mcart_1 @ sk_A) != (sk_D_1))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['20', '31'])).
% 0.46/0.65  thf('33', plain, ((r2_hidden @ sk_C @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['18', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.65  thf('35', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.46/0.65         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.46/0.65      inference('split', [status(esa)], ['26'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['26'])).
% 0.46/0.65  thf('38', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['29', '37'])).
% 0.46/0.65  thf('39', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.46/0.65  thf('40', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['35', '39'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.52/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
