%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JCzolFlXLn

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  354 ( 769 expanded)
%              Number of equality atoms :   42 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X17 @ X14 ) @ ( sk_D @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X9 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X8 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('10',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('13',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X20 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','27'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('36',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','36'])).

thf('38',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JCzolFlXLn
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 209 iterations in 0.115s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(cc1_relat_1, axiom,
% 0.21/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.56  thf('0', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.56  thf(t37_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.56         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X22 : $i]:
% 0.21/0.56         (((k2_relat_1 @ X22) = (k1_relat_1 @ (k4_relat_1 @ X22)))
% 0.21/0.56          | ~ (v1_relat_1 @ X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.56  thf('2', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.56  thf(d4_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X14 : $i, X17 : $i]:
% 0.21/0.56         (((X17) = (k1_relat_1 @ X14))
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k4_tarski @ (sk_C @ X17 @ X14) @ (sk_D @ X17 @ X14)) @ X14)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X17 @ X14) @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.56  thf(t4_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.56  thf(t64_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (((X7) != (X9))
% 0.21/0.56          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ (k1_tarski @ X9))))),
% 0.21/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]:
% 0.21/0.56         ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X8 @ (k1_tarski @ X9)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.56  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.56          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.56  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.56  thf('10', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X22 : $i]:
% 0.21/0.56         (((k1_relat_1 @ X22) = (k2_relat_1 @ (k4_relat_1 @ X22)))
% 0.21/0.56          | ~ (v1_relat_1 @ X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.56          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.56  thf('13', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf(t18_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_1 @ X20) @ (k2_relat_1 @ X20))
% 0.21/0.56          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r2_hidden @ (sk_C_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf(d1_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ((k1_relat_1 @ (k4_relat_1 @ X0)) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.56        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.21/0.56        | ((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.21/0.56        | ((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf(dt_k4_relat_1, axiom,
% 0.21/0.56    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.56        | ((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.56        | ((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '24'])).
% 0.21/0.56  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (((k1_relat_1 @ (k4_relat_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['1', '27'])).
% 0.21/0.56  thf(t60_relat_1, conjecture,
% 0.21/0.56    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.56     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.56        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.56        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['29'])).
% 0.21/0.56  thf('31', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['29'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.56       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.56      inference('split', [status(esa)], ['29'])).
% 0.21/0.56  thf('36', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['30', '36'])).
% 0.21/0.56  thf('38', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['28', '37'])).
% 0.21/0.56  thf('39', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '38'])).
% 0.21/0.56  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('41', plain, ($false), inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
