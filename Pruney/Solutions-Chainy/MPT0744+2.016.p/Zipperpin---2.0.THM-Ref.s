%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tMgryE2uM3

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:02 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  450 ( 903 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_ordinal1 @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( r1_ordinal1 @ X38 @ X37 )
      | ( r2_hidden @ X37 @ X38 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( r2_hidden @ X35 @ X34 )
      | ~ ( r2_hidden @ X35 @ ( k1_ordinal1 @ X34 ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( r1_ordinal1 @ X38 @ X37 )
      | ( r2_hidden @ X37 @ X38 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ ( k1_ordinal1 @ X36 ) )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_ordinal1 @ X32 @ X33 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_ordinal1 @ X32 )
      | ~ ( v3_ordinal1 @ X33 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_ordinal1 @ X32 @ X33 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ ( k1_ordinal1 @ X36 ) )
      | ( X35 != X36 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('51',plain,(
    ! [X36: $i] :
      ( r2_hidden @ X36 @ ( k1_ordinal1 @ X36 ) ) ),
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
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tMgryE2uM3
% 0.18/0.37  % Computer   : n013.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 16:48:25 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.37  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 440 iterations in 0.222s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.50/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.70  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.50/0.70  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.70  thf(t34_ordinal1, conjecture,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.70           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.70             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i]:
% 0.50/0.70        ( ( v3_ordinal1 @ A ) =>
% 0.50/0.70          ( ![B:$i]:
% 0.50/0.70            ( ( v3_ordinal1 @ B ) =>
% 0.50/0.70              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.70                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.50/0.70  thf('0', plain,
% 0.50/0.70      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.50/0.70        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('1', plain,
% 0.50/0.70      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.70       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.70      inference('split', [status(esa)], ['0'])).
% 0.50/0.70  thf(d10_xboole_0, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.50/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.70  thf('3', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.50/0.70      inference('simplify', [status(thm)], ['2'])).
% 0.50/0.70  thf(redefinition_r1_ordinal1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.50/0.70       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.50/0.70  thf('4', plain,
% 0.50/0.70      (![X32 : $i, X33 : $i]:
% 0.50/0.70         (~ (v3_ordinal1 @ X32)
% 0.50/0.70          | ~ (v3_ordinal1 @ X33)
% 0.50/0.70          | (r1_ordinal1 @ X32 @ X33)
% 0.50/0.70          | ~ (r1_tarski @ X32 @ X33))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.70  thf('5', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.50/0.70  thf('6', plain,
% 0.50/0.70      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.70  thf(t26_ordinal1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.70           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      (![X37 : $i, X38 : $i]:
% 0.50/0.70         (~ (v3_ordinal1 @ X37)
% 0.50/0.70          | (r1_ordinal1 @ X38 @ X37)
% 0.50/0.70          | (r2_hidden @ X37 @ X38)
% 0.50/0.70          | ~ (v3_ordinal1 @ X38))),
% 0.50/0.70      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.50/0.70  thf('8', plain,
% 0.50/0.70      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('split', [status(esa)], ['8'])).
% 0.50/0.70  thf(t13_ordinal1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.70       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (![X34 : $i, X35 : $i]:
% 0.50/0.70         (((X35) = (X34))
% 0.50/0.70          | (r2_hidden @ X35 @ X34)
% 0.50/0.70          | ~ (r2_hidden @ X35 @ (k1_ordinal1 @ X34)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.50/0.70  thf('11', plain,
% 0.50/0.70      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.50/0.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf(antisymmetry_r2_hidden, axiom,
% 0.50/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.50/0.70  thf('12', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.50/0.70  thf('13', plain,
% 0.50/0.70      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.50/0.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.70  thf('14', plain,
% 0.50/0.70      (((~ (v3_ordinal1 @ sk_A)
% 0.50/0.70         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.50/0.70         | ~ (v3_ordinal1 @ sk_B)
% 0.50/0.70         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['7', '13'])).
% 0.50/0.70  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('17', plain,
% 0.50/0.70      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.50/0.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('split', [status(esa)], ['0'])).
% 0.50/0.70  thf('19', plain,
% 0.50/0.70      ((((sk_A) = (sk_B)))
% 0.50/0.70         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.70             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('20', plain,
% 0.50/0.70      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('split', [status(esa)], ['0'])).
% 0.50/0.70  thf('21', plain,
% 0.50/0.70      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.50/0.70         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.70             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      ((~ (v3_ordinal1 @ sk_A))
% 0.50/0.70         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.70             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['6', '21'])).
% 0.50/0.70  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.70       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.70       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.70      inference('split', [status(esa)], ['8'])).
% 0.50/0.70  thf('26', plain,
% 0.50/0.70      (![X37 : $i, X38 : $i]:
% 0.50/0.70         (~ (v3_ordinal1 @ X37)
% 0.50/0.70          | (r1_ordinal1 @ X38 @ X37)
% 0.50/0.70          | (r2_hidden @ X37 @ X38)
% 0.50/0.70          | ~ (v3_ordinal1 @ X38))),
% 0.50/0.70      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.50/0.70  thf('27', plain,
% 0.50/0.70      (![X35 : $i, X36 : $i]:
% 0.50/0.70         ((r2_hidden @ X35 @ (k1_ordinal1 @ X36)) | ~ (r2_hidden @ X35 @ X36))),
% 0.50/0.70      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         (~ (v3_ordinal1 @ X0)
% 0.50/0.70          | (r1_ordinal1 @ X0 @ X1)
% 0.50/0.70          | ~ (v3_ordinal1 @ X1)
% 0.50/0.70          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.70  thf('29', plain,
% 0.50/0.70      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('split', [status(esa)], ['0'])).
% 0.50/0.70  thf('30', plain,
% 0.50/0.70      (((~ (v3_ordinal1 @ sk_A)
% 0.50/0.70         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.50/0.70         | ~ (v3_ordinal1 @ sk_B)))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.70  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.50/0.70  thf('34', plain,
% 0.50/0.70      (![X32 : $i, X33 : $i]:
% 0.50/0.70         (~ (v3_ordinal1 @ X32)
% 0.50/0.70          | ~ (v3_ordinal1 @ X33)
% 0.50/0.70          | (r1_tarski @ X32 @ X33)
% 0.50/0.70          | ~ (r1_ordinal1 @ X32 @ X33))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.70  thf('35', plain,
% 0.50/0.70      ((((r1_tarski @ sk_B @ sk_A)
% 0.50/0.70         | ~ (v3_ordinal1 @ sk_A)
% 0.50/0.70         | ~ (v3_ordinal1 @ sk_B)))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.70  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('38', plain,
% 0.50/0.70      (((r1_tarski @ sk_B @ sk_A))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('split', [status(esa)], ['8'])).
% 0.50/0.70  thf('40', plain,
% 0.50/0.70      (![X32 : $i, X33 : $i]:
% 0.50/0.70         (~ (v3_ordinal1 @ X32)
% 0.50/0.70          | ~ (v3_ordinal1 @ X33)
% 0.50/0.70          | (r1_tarski @ X32 @ X33)
% 0.50/0.70          | ~ (r1_ordinal1 @ X32 @ X33))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.70  thf('41', plain,
% 0.50/0.70      ((((r1_tarski @ sk_A @ sk_B)
% 0.50/0.70         | ~ (v3_ordinal1 @ sk_B)
% 0.50/0.70         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.70  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('44', plain,
% 0.50/0.70      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.50/0.70  thf('45', plain,
% 0.50/0.70      (![X8 : $i, X10 : $i]:
% 0.50/0.70         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.50/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.50/0.70         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.50/0.70  thf('47', plain,
% 0.50/0.70      ((((sk_B) = (sk_A)))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.50/0.70             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['38', '46'])).
% 0.50/0.70  thf('48', plain,
% 0.50/0.70      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.70      inference('split', [status(esa)], ['0'])).
% 0.50/0.70  thf('49', plain,
% 0.50/0.70      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.50/0.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.50/0.70             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.70  thf('50', plain,
% 0.50/0.70      (![X35 : $i, X36 : $i]:
% 0.50/0.70         ((r2_hidden @ X35 @ (k1_ordinal1 @ X36)) | ((X35) != (X36)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.50/0.70  thf('51', plain, (![X36 : $i]: (r2_hidden @ X36 @ (k1_ordinal1 @ X36))),
% 0.50/0.70      inference('simplify', [status(thm)], ['50'])).
% 0.50/0.70  thf('52', plain,
% 0.50/0.70      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.70       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.70      inference('demod', [status(thm)], ['49', '51'])).
% 0.50/0.70  thf('53', plain, ($false),
% 0.50/0.70      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '52'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
