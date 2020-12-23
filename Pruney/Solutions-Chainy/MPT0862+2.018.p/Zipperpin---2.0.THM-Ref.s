%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvDgKt4xKj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  390 ( 748 expanded)
%              Number of equality atoms :   49 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k4_tarski @ X31 @ X32 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X33 ) @ X35 )
      | ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('5',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X34 @ X35 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X31 @ X32 ) ) @ X35 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X31 @ X32 ) ) @ X34 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('6',plain,(
    ! [X43: $i,X45: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X43 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X43 @ X44 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X34 @ X35 ) )
      | ~ ( r2_hidden @ X32 @ X35 )
      | ~ ( r2_hidden @ X31 @ X34 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_mcart_1 @ X36 )
        = X38 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ ( k1_tarski @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('12',plain,
    ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X43: $i,X45: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X43 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_mcart_1 @ X39 )
        = X42 )
      | ( ( k2_mcart_1 @ X39 )
        = X41 )
      | ~ ( r2_hidden @ X39 @ ( k2_zfmisc_1 @ X40 @ ( k2_tarski @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,
    ( ( ( sk_D != sk_D )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_C ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('27',plain,
    ( ( sk_C != sk_C )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_D )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['17','19','28'])).

thf('30',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['16','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvDgKt4xKj
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 44 iterations in 0.021s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(t18_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @
% 0.20/0.48         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.48       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.48         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( r2_hidden @
% 0.20/0.48            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.48          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.48            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ 
% 0.20/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t10_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X28) @ X29)
% 0.20/0.48          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('2', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t11_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.20/0.48       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.20/0.48         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.48         (((X33) != (k4_tarski @ X31 @ X32))
% 0.20/0.48          | ~ (r2_hidden @ (k1_mcart_1 @ X33) @ X34)
% 0.20/0.48          | ~ (r2_hidden @ (k2_mcart_1 @ X33) @ X35)
% 0.20/0.48          | (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X34 : $i, X35 : $i]:
% 0.20/0.48         ((r2_hidden @ (k4_tarski @ X31 @ X32) @ (k2_zfmisc_1 @ X34 @ X35))
% 0.20/0.48          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X31 @ X32)) @ X35)
% 0.20/0.48          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X31 @ X32)) @ X34))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf(t7_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X43 : $i, X45 : $i]: ((k2_mcart_1 @ (k4_tarski @ X43 @ X45)) = (X45))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X43 : $i, X44 : $i]: ((k1_mcart_1 @ (k4_tarski @ X43 @ X44)) = (X43))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X34 : $i, X35 : $i]:
% 0.20/0.48         ((r2_hidden @ (k4_tarski @ X31 @ X32) @ (k2_zfmisc_1 @ X34 @ X35))
% 0.20/0.48          | ~ (r2_hidden @ X32 @ X35)
% 0.20/0.48          | ~ (r2_hidden @ X31 @ X34))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.48          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48             (k2_zfmisc_1 @ X0 @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.20/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.48  thf(t13_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.48         (((k2_mcart_1 @ X36) = (X38))
% 0.20/0.48          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ (k1_tarski @ X38))))),
% 0.20/0.48      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((k2_mcart_1 @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.20/0.48         = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X43 : $i, X45 : $i]: ((k2_mcart_1 @ (k4_tarski @ X43 @ X45)) = (X45))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('14', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.48      inference('split', [status(esa)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ 
% 0.20/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t16_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.48         (((k2_mcart_1 @ X39) = (X42))
% 0.20/0.48          | ((k2_mcart_1 @ X39) = (X41))
% 0.20/0.48          | ~ (r2_hidden @ X39 @ (k2_zfmisc_1 @ X40 @ (k2_tarski @ X41 @ X42))))),
% 0.20/0.48      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['18'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((((sk_D) != (sk_D)) | ((k2_mcart_1 @ sk_A) = (sk_C))))
% 0.20/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) = (sk_C))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((sk_C) != (sk_C)))
% 0.20/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))) & 
% 0.20/0.48             ~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_A) = (sk_C))) | (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.48  thf('29', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['17', '19', '28'])).
% 0.20/0.48  thf('30', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['16', '29'])).
% 0.20/0.48  thf('31', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['14', '30'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
