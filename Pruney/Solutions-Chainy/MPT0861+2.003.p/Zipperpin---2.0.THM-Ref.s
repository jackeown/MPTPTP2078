%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hNNcZA8zHw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:51 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 149 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  426 (1310 expanded)
%              Number of equality atoms :   44 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ ( k2_tarski @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X26 )
        = ( k2_tarski @ X23 @ X25 ) )
      | ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X22 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['22','33'])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('37',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['28'])).

thf('39',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('40',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['31','39'])).

thf('41',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['38','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hNNcZA8zHw
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.17/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.17/1.37  % Solved by: fo/fo7.sh
% 1.17/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.17/1.37  % done 1408 iterations in 0.917s
% 1.17/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.17/1.37  % SZS output start Refutation
% 1.17/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.17/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.17/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.17/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.17/1.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.17/1.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.17/1.37  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.17/1.37  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.17/1.37  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.17/1.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.17/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.17/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.17/1.37  thf(t69_enumset1, axiom,
% 1.17/1.37    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.17/1.37  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.17/1.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.17/1.37  thf(d10_xboole_0, axiom,
% 1.17/1.37    (![A:$i,B:$i]:
% 1.17/1.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.17/1.37  thf('1', plain,
% 1.17/1.37      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.17/1.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.17/1.37  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.17/1.37      inference('simplify', [status(thm)], ['1'])).
% 1.17/1.37  thf(t38_zfmisc_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.17/1.37       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.17/1.37  thf('3', plain,
% 1.17/1.37      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.17/1.37         ((r2_hidden @ X15 @ X16)
% 1.17/1.37          | ~ (r1_tarski @ (k2_tarski @ X15 @ X17) @ X16))),
% 1.17/1.37      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.17/1.37  thf('4', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.17/1.37      inference('sup-', [status(thm)], ['2', '3'])).
% 1.17/1.37  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.17/1.37      inference('sup+', [status(thm)], ['0', '4'])).
% 1.17/1.37  thf(t17_mcart_1, conjecture,
% 1.17/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.37     ( ( r2_hidden @
% 1.17/1.37         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 1.17/1.37       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 1.17/1.37         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 1.17/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.17/1.37    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.37        ( ( r2_hidden @
% 1.17/1.37            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 1.17/1.37          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 1.17/1.37            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 1.17/1.37    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 1.17/1.37  thf('6', plain,
% 1.17/1.37      ((r2_hidden @ sk_A @ 
% 1.17/1.37        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf(t10_mcart_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.17/1.37       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.17/1.37         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.17/1.37  thf('7', plain,
% 1.17/1.37      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.17/1.37         ((r2_hidden @ (k1_mcart_1 @ X27) @ X28)
% 1.17/1.37          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 1.17/1.37      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.17/1.37  thf('8', plain,
% 1.17/1.37      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 1.17/1.37      inference('sup-', [status(thm)], ['6', '7'])).
% 1.17/1.37  thf(t72_zfmisc_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.17/1.37       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 1.17/1.37  thf('9', plain,
% 1.17/1.37      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.17/1.37         (((k4_xboole_0 @ (k2_tarski @ X23 @ X25) @ X26)
% 1.17/1.37            = (k2_tarski @ X23 @ X25))
% 1.17/1.37          | (r2_hidden @ X25 @ X26)
% 1.17/1.37          | (r2_hidden @ X23 @ X26))),
% 1.17/1.37      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 1.17/1.37  thf(d5_xboole_0, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.17/1.37       ( ![D:$i]:
% 1.17/1.37         ( ( r2_hidden @ D @ C ) <=>
% 1.17/1.37           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.17/1.37  thf('10', plain,
% 1.17/1.37      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.37         (~ (r2_hidden @ X4 @ X3)
% 1.17/1.37          | ~ (r2_hidden @ X4 @ X2)
% 1.17/1.37          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.37      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.17/1.37  thf('11', plain,
% 1.17/1.37      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.17/1.37         (~ (r2_hidden @ X4 @ X2)
% 1.17/1.37          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.37      inference('simplify', [status(thm)], ['10'])).
% 1.17/1.37  thf('12', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.37         (~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 1.17/1.37          | (r2_hidden @ X1 @ X2)
% 1.17/1.37          | (r2_hidden @ X0 @ X2)
% 1.17/1.37          | ~ (r2_hidden @ X3 @ X2))),
% 1.17/1.37      inference('sup-', [status(thm)], ['9', '11'])).
% 1.17/1.37  thf('13', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 1.17/1.37          | (r2_hidden @ sk_C @ X0)
% 1.17/1.37          | (r2_hidden @ sk_B @ X0))),
% 1.17/1.37      inference('sup-', [status(thm)], ['8', '12'])).
% 1.17/1.37  thf('14', plain,
% 1.17/1.37      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.17/1.37        | (r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.17/1.37      inference('sup-', [status(thm)], ['5', '13'])).
% 1.17/1.37  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.17/1.37      inference('sup+', [status(thm)], ['0', '4'])).
% 1.17/1.37  thf(t64_zfmisc_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.17/1.37       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.17/1.37  thf('16', plain,
% 1.17/1.37      (![X19 : $i, X20 : $i, X22 : $i]:
% 1.17/1.37         ((r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X22)))
% 1.17/1.37          | ((X19) = (X22))
% 1.17/1.37          | ~ (r2_hidden @ X19 @ X20))),
% 1.17/1.37      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.17/1.37  thf('17', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (((X0) = (X1))
% 1.17/1.37          | (r2_hidden @ X0 @ 
% 1.17/1.37             (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 1.17/1.37      inference('sup-', [status(thm)], ['15', '16'])).
% 1.17/1.37  thf('18', plain,
% 1.17/1.37      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.17/1.37         (~ (r2_hidden @ X4 @ X2)
% 1.17/1.37          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.37      inference('simplify', [status(thm)], ['10'])).
% 1.17/1.37  thf('19', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.17/1.37  thf('20', plain,
% 1.17/1.37      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.17/1.37        | ((sk_C) = (k1_mcart_1 @ sk_A)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['14', '19'])).
% 1.17/1.37  thf('21', plain,
% 1.17/1.37      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('22', plain,
% 1.17/1.37      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 1.17/1.37         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 1.17/1.37      inference('split', [status(esa)], ['21'])).
% 1.17/1.37  thf('23', plain,
% 1.17/1.37      ((r2_hidden @ sk_A @ 
% 1.17/1.37        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('24', plain,
% 1.17/1.37      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.17/1.37         ((r2_hidden @ (k2_mcart_1 @ X27) @ X29)
% 1.17/1.37          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 1.17/1.37      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.17/1.37  thf('25', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.17/1.37      inference('sup-', [status(thm)], ['23', '24'])).
% 1.17/1.37  thf('26', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.17/1.37  thf('27', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 1.17/1.37      inference('sup-', [status(thm)], ['25', '26'])).
% 1.17/1.37  thf('28', plain,
% 1.17/1.37      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('29', plain,
% 1.17/1.37      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 1.17/1.37         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 1.17/1.37      inference('split', [status(esa)], ['28'])).
% 1.17/1.37  thf('30', plain,
% 1.17/1.37      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 1.17/1.37      inference('sup-', [status(thm)], ['27', '29'])).
% 1.17/1.37  thf('31', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 1.17/1.37      inference('simplify', [status(thm)], ['30'])).
% 1.17/1.37  thf('32', plain,
% 1.17/1.37      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 1.17/1.37       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 1.17/1.37      inference('split', [status(esa)], ['21'])).
% 1.17/1.37  thf('33', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 1.17/1.37      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 1.17/1.37  thf('34', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 1.17/1.37      inference('simpl_trail', [status(thm)], ['22', '33'])).
% 1.17/1.37  thf('35', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 1.17/1.37      inference('simplify_reflect-', [status(thm)], ['20', '34'])).
% 1.17/1.37  thf('36', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.17/1.37  thf('37', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 1.17/1.37      inference('sup-', [status(thm)], ['35', '36'])).
% 1.17/1.37  thf('38', plain,
% 1.17/1.37      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 1.17/1.37         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 1.17/1.37      inference('split', [status(esa)], ['28'])).
% 1.17/1.37  thf('39', plain,
% 1.17/1.37      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 1.17/1.37       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 1.17/1.37      inference('split', [status(esa)], ['28'])).
% 1.17/1.37  thf('40', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 1.17/1.37      inference('sat_resolution*', [status(thm)], ['31', '39'])).
% 1.17/1.37  thf('41', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 1.17/1.37      inference('simpl_trail', [status(thm)], ['38', '40'])).
% 1.17/1.37  thf('42', plain, ($false),
% 1.17/1.37      inference('simplify_reflect-', [status(thm)], ['37', '41'])).
% 1.17/1.37  
% 1.17/1.37  % SZS output end Refutation
% 1.17/1.37  
% 1.17/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
