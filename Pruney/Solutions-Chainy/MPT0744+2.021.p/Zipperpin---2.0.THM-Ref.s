%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Uv5gW74QGf

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:02 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  450 ( 903 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_ordinal1 @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ X25 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('8',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_ordinal1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('11',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('13',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ X25 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('35',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ( X20 != X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('51',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_ordinal1 @ X21 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Uv5gW74QGf
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:39:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.21/1.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.21/1.39  % Solved by: fo/fo7.sh
% 1.21/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.39  % done 1675 iterations in 0.932s
% 1.21/1.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.21/1.39  % SZS output start Refutation
% 1.21/1.39  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.21/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.39  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.21/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.39  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.21/1.39  thf(t34_ordinal1, conjecture,
% 1.21/1.39    (![A:$i]:
% 1.21/1.39     ( ( v3_ordinal1 @ A ) =>
% 1.21/1.39       ( ![B:$i]:
% 1.21/1.39         ( ( v3_ordinal1 @ B ) =>
% 1.21/1.39           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.21/1.39             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 1.21/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.39    (~( ![A:$i]:
% 1.21/1.39        ( ( v3_ordinal1 @ A ) =>
% 1.21/1.39          ( ![B:$i]:
% 1.21/1.39            ( ( v3_ordinal1 @ B ) =>
% 1.21/1.39              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.21/1.39                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 1.21/1.39    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 1.21/1.39  thf('0', plain,
% 1.21/1.39      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 1.21/1.39        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('1', plain,
% 1.21/1.39      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.21/1.39       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.21/1.39      inference('split', [status(esa)], ['0'])).
% 1.21/1.39  thf(d10_xboole_0, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.21/1.39  thf('2', plain,
% 1.21/1.39      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.21/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.21/1.39  thf('3', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.21/1.39      inference('simplify', [status(thm)], ['2'])).
% 1.21/1.39  thf(redefinition_r1_ordinal1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.21/1.39       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.21/1.39  thf('4', plain,
% 1.21/1.39      (![X17 : $i, X18 : $i]:
% 1.21/1.39         (~ (v3_ordinal1 @ X17)
% 1.21/1.39          | ~ (v3_ordinal1 @ X18)
% 1.21/1.39          | (r1_ordinal1 @ X17 @ X18)
% 1.21/1.39          | ~ (r1_tarski @ X17 @ X18))),
% 1.21/1.39      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.21/1.39  thf('5', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 1.21/1.39      inference('sup-', [status(thm)], ['3', '4'])).
% 1.21/1.39  thf('6', plain,
% 1.21/1.39      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 1.21/1.39      inference('simplify', [status(thm)], ['5'])).
% 1.21/1.39  thf(t26_ordinal1, axiom,
% 1.21/1.39    (![A:$i]:
% 1.21/1.39     ( ( v3_ordinal1 @ A ) =>
% 1.21/1.39       ( ![B:$i]:
% 1.21/1.39         ( ( v3_ordinal1 @ B ) =>
% 1.21/1.39           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.21/1.39  thf('7', plain,
% 1.21/1.39      (![X24 : $i, X25 : $i]:
% 1.21/1.39         (~ (v3_ordinal1 @ X24)
% 1.21/1.39          | (r1_ordinal1 @ X25 @ X24)
% 1.21/1.39          | (r2_hidden @ X24 @ X25)
% 1.21/1.39          | ~ (v3_ordinal1 @ X25))),
% 1.21/1.39      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.21/1.39  thf('8', plain,
% 1.21/1.39      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('9', plain,
% 1.21/1.39      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.21/1.39         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('split', [status(esa)], ['8'])).
% 1.21/1.39  thf(t13_ordinal1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.21/1.39       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 1.21/1.39  thf('10', plain,
% 1.21/1.39      (![X19 : $i, X20 : $i]:
% 1.21/1.39         (((X20) = (X19))
% 1.21/1.39          | (r2_hidden @ X20 @ X19)
% 1.21/1.39          | ~ (r2_hidden @ X20 @ (k1_ordinal1 @ X19)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.21/1.39  thf('11', plain,
% 1.21/1.39      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 1.21/1.39         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['9', '10'])).
% 1.21/1.39  thf(antisymmetry_r2_hidden, axiom,
% 1.21/1.39    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.21/1.39  thf('12', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.21/1.39      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.21/1.39  thf('13', plain,
% 1.21/1.39      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 1.21/1.39         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['11', '12'])).
% 1.21/1.39  thf('14', plain,
% 1.21/1.39      (((~ (v3_ordinal1 @ sk_A)
% 1.21/1.39         | (r1_ordinal1 @ sk_A @ sk_B)
% 1.21/1.39         | ~ (v3_ordinal1 @ sk_B)
% 1.21/1.39         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['7', '13'])).
% 1.21/1.39  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('17', plain,
% 1.21/1.39      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 1.21/1.39         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.21/1.39  thf('18', plain,
% 1.21/1.39      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('split', [status(esa)], ['0'])).
% 1.21/1.39  thf('19', plain,
% 1.21/1.39      ((((sk_A) = (sk_B)))
% 1.21/1.39         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.21/1.39             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['17', '18'])).
% 1.21/1.39  thf('20', plain,
% 1.21/1.39      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('split', [status(esa)], ['0'])).
% 1.21/1.39  thf('21', plain,
% 1.21/1.39      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 1.21/1.39         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.21/1.39             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['19', '20'])).
% 1.21/1.39  thf('22', plain,
% 1.21/1.39      ((~ (v3_ordinal1 @ sk_A))
% 1.21/1.39         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.21/1.39             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['6', '21'])).
% 1.21/1.39  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('24', plain,
% 1.21/1.39      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.21/1.39       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.21/1.39      inference('demod', [status(thm)], ['22', '23'])).
% 1.21/1.39  thf('25', plain,
% 1.21/1.39      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.21/1.39       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.21/1.39      inference('split', [status(esa)], ['8'])).
% 1.21/1.39  thf('26', plain,
% 1.21/1.39      (![X24 : $i, X25 : $i]:
% 1.21/1.39         (~ (v3_ordinal1 @ X24)
% 1.21/1.39          | (r1_ordinal1 @ X25 @ X24)
% 1.21/1.39          | (r2_hidden @ X24 @ X25)
% 1.21/1.39          | ~ (v3_ordinal1 @ X25))),
% 1.21/1.39      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.21/1.39  thf('27', plain,
% 1.21/1.39      (![X20 : $i, X21 : $i]:
% 1.21/1.39         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ~ (r2_hidden @ X20 @ X21))),
% 1.21/1.39      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.21/1.39  thf('28', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         (~ (v3_ordinal1 @ X0)
% 1.21/1.39          | (r1_ordinal1 @ X0 @ X1)
% 1.21/1.39          | ~ (v3_ordinal1 @ X1)
% 1.21/1.39          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['26', '27'])).
% 1.21/1.39  thf('29', plain,
% 1.21/1.39      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('split', [status(esa)], ['0'])).
% 1.21/1.39  thf('30', plain,
% 1.21/1.39      (((~ (v3_ordinal1 @ sk_A)
% 1.21/1.39         | (r1_ordinal1 @ sk_B @ sk_A)
% 1.21/1.39         | ~ (v3_ordinal1 @ sk_B)))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['28', '29'])).
% 1.21/1.39  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('33', plain,
% 1.21/1.39      (((r1_ordinal1 @ sk_B @ sk_A))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.21/1.39  thf('34', plain,
% 1.21/1.39      (![X17 : $i, X18 : $i]:
% 1.21/1.39         (~ (v3_ordinal1 @ X17)
% 1.21/1.39          | ~ (v3_ordinal1 @ X18)
% 1.21/1.39          | (r1_tarski @ X17 @ X18)
% 1.21/1.39          | ~ (r1_ordinal1 @ X17 @ X18))),
% 1.21/1.39      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.21/1.39  thf('35', plain,
% 1.21/1.39      ((((r1_tarski @ sk_B @ sk_A)
% 1.21/1.39         | ~ (v3_ordinal1 @ sk_A)
% 1.21/1.39         | ~ (v3_ordinal1 @ sk_B)))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('sup-', [status(thm)], ['33', '34'])).
% 1.21/1.39  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('38', plain,
% 1.21/1.39      (((r1_tarski @ sk_B @ sk_A))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.21/1.39  thf('39', plain,
% 1.21/1.39      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('split', [status(esa)], ['8'])).
% 1.21/1.39  thf('40', plain,
% 1.21/1.39      (![X17 : $i, X18 : $i]:
% 1.21/1.39         (~ (v3_ordinal1 @ X17)
% 1.21/1.39          | ~ (v3_ordinal1 @ X18)
% 1.21/1.39          | (r1_tarski @ X17 @ X18)
% 1.21/1.39          | ~ (r1_ordinal1 @ X17 @ X18))),
% 1.21/1.39      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.21/1.39  thf('41', plain,
% 1.21/1.39      ((((r1_tarski @ sk_A @ sk_B)
% 1.21/1.39         | ~ (v3_ordinal1 @ sk_B)
% 1.21/1.39         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['39', '40'])).
% 1.21/1.39  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf('44', plain,
% 1.21/1.39      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.21/1.39  thf('45', plain,
% 1.21/1.39      (![X8 : $i, X10 : $i]:
% 1.21/1.39         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.21/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.21/1.39  thf('46', plain,
% 1.21/1.39      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 1.21/1.39         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['44', '45'])).
% 1.21/1.39  thf('47', plain,
% 1.21/1.39      ((((sk_B) = (sk_A)))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.21/1.39             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['38', '46'])).
% 1.21/1.39  thf('48', plain,
% 1.21/1.39      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.21/1.39      inference('split', [status(esa)], ['0'])).
% 1.21/1.39  thf('49', plain,
% 1.21/1.39      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 1.21/1.39         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.21/1.39             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('sup-', [status(thm)], ['47', '48'])).
% 1.21/1.39  thf('50', plain,
% 1.21/1.39      (![X20 : $i, X21 : $i]:
% 1.21/1.39         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ((X20) != (X21)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.21/1.39  thf('51', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_ordinal1 @ X21))),
% 1.21/1.39      inference('simplify', [status(thm)], ['50'])).
% 1.21/1.39  thf('52', plain,
% 1.21/1.39      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.21/1.39       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.21/1.39      inference('demod', [status(thm)], ['49', '51'])).
% 1.21/1.39  thf('53', plain, ($false),
% 1.21/1.39      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '52'])).
% 1.21/1.39  
% 1.21/1.39  % SZS output end Refutation
% 1.21/1.39  
% 1.21/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
