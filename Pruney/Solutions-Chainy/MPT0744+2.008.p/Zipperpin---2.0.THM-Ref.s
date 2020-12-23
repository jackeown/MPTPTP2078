%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.50iVCymh6b

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:00 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  450 ( 903 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ( r1_ordinal1 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ X29 )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( X26 = X25 )
      | ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X26 @ ( k1_ordinal1 @ X25 ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ( r1_ordinal1 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ X29 )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k1_ordinal1 @ X27 ) )
      | ( X26 != X27 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('51',plain,(
    ! [X27: $i] :
      ( r2_hidden @ X27 @ ( k1_ordinal1 @ X27 ) ) ),
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
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.50iVCymh6b
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:40:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 2.22/2.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.22/2.48  % Solved by: fo/fo7.sh
% 2.22/2.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.48  % done 3175 iterations in 2.016s
% 2.22/2.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.22/2.48  % SZS output start Refutation
% 2.22/2.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.22/2.48  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 2.22/2.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 2.22/2.48  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 2.22/2.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.22/2.48  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.48  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.48  thf(t34_ordinal1, conjecture,
% 2.22/2.48    (![A:$i]:
% 2.22/2.48     ( ( v3_ordinal1 @ A ) =>
% 2.22/2.48       ( ![B:$i]:
% 2.22/2.48         ( ( v3_ordinal1 @ B ) =>
% 2.22/2.48           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.22/2.48             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 2.22/2.48  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.48    (~( ![A:$i]:
% 2.22/2.48        ( ( v3_ordinal1 @ A ) =>
% 2.22/2.48          ( ![B:$i]:
% 2.22/2.48            ( ( v3_ordinal1 @ B ) =>
% 2.22/2.48              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.22/2.48                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 2.22/2.48    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 2.22/2.48  thf('0', plain,
% 2.22/2.48      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 2.22/2.48        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('1', plain,
% 2.22/2.48      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.22/2.48       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.22/2.48      inference('split', [status(esa)], ['0'])).
% 2.22/2.48  thf(d10_xboole_0, axiom,
% 2.22/2.48    (![A:$i,B:$i]:
% 2.22/2.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.22/2.48  thf('2', plain,
% 2.22/2.48      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 2.22/2.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.48  thf('3', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 2.22/2.48      inference('simplify', [status(thm)], ['2'])).
% 2.22/2.48  thf(redefinition_r1_ordinal1, axiom,
% 2.22/2.48    (![A:$i,B:$i]:
% 2.22/2.48     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 2.22/2.48       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 2.22/2.48  thf('4', plain,
% 2.22/2.48      (![X23 : $i, X24 : $i]:
% 2.22/2.48         (~ (v3_ordinal1 @ X23)
% 2.22/2.48          | ~ (v3_ordinal1 @ X24)
% 2.22/2.48          | (r1_ordinal1 @ X23 @ X24)
% 2.22/2.48          | ~ (r1_tarski @ X23 @ X24))),
% 2.22/2.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.22/2.48  thf('5', plain,
% 2.22/2.48      (![X0 : $i]:
% 2.22/2.48         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 2.22/2.48      inference('sup-', [status(thm)], ['3', '4'])).
% 2.22/2.48  thf('6', plain,
% 2.22/2.48      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 2.22/2.48      inference('simplify', [status(thm)], ['5'])).
% 2.22/2.48  thf(t26_ordinal1, axiom,
% 2.22/2.48    (![A:$i]:
% 2.22/2.48     ( ( v3_ordinal1 @ A ) =>
% 2.22/2.48       ( ![B:$i]:
% 2.22/2.48         ( ( v3_ordinal1 @ B ) =>
% 2.22/2.48           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 2.22/2.48  thf('7', plain,
% 2.22/2.48      (![X28 : $i, X29 : $i]:
% 2.22/2.48         (~ (v3_ordinal1 @ X28)
% 2.22/2.48          | (r1_ordinal1 @ X29 @ X28)
% 2.22/2.48          | (r2_hidden @ X28 @ X29)
% 2.22/2.48          | ~ (v3_ordinal1 @ X29))),
% 2.22/2.48      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.22/2.48  thf('8', plain,
% 2.22/2.48      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('9', plain,
% 2.22/2.48      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 2.22/2.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('split', [status(esa)], ['8'])).
% 2.22/2.48  thf(t13_ordinal1, axiom,
% 2.22/2.48    (![A:$i,B:$i]:
% 2.22/2.48     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 2.22/2.48       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 2.22/2.48  thf('10', plain,
% 2.22/2.48      (![X25 : $i, X26 : $i]:
% 2.22/2.48         (((X26) = (X25))
% 2.22/2.48          | (r2_hidden @ X26 @ X25)
% 2.22/2.48          | ~ (r2_hidden @ X26 @ (k1_ordinal1 @ X25)))),
% 2.22/2.48      inference('cnf', [status(esa)], [t13_ordinal1])).
% 2.22/2.48  thf('11', plain,
% 2.22/2.48      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 2.22/2.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['9', '10'])).
% 2.22/2.48  thf(antisymmetry_r2_hidden, axiom,
% 2.22/2.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 2.22/2.48  thf('12', plain,
% 2.22/2.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 2.22/2.48      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 2.22/2.48  thf('13', plain,
% 2.22/2.48      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 2.22/2.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['11', '12'])).
% 2.22/2.48  thf('14', plain,
% 2.22/2.48      (((~ (v3_ordinal1 @ sk_A)
% 2.22/2.48         | (r1_ordinal1 @ sk_A @ sk_B)
% 2.22/2.48         | ~ (v3_ordinal1 @ sk_B)
% 2.22/2.48         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['7', '13'])).
% 2.22/2.48  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('17', plain,
% 2.22/2.48      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 2.22/2.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('demod', [status(thm)], ['14', '15', '16'])).
% 2.22/2.48  thf('18', plain,
% 2.22/2.48      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('split', [status(esa)], ['0'])).
% 2.22/2.48  thf('19', plain,
% 2.22/2.48      ((((sk_A) = (sk_B)))
% 2.22/2.48         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 2.22/2.48             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['17', '18'])).
% 2.22/2.48  thf('20', plain,
% 2.22/2.48      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('split', [status(esa)], ['0'])).
% 2.22/2.48  thf('21', plain,
% 2.22/2.48      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 2.22/2.48         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 2.22/2.48             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['19', '20'])).
% 2.22/2.48  thf('22', plain,
% 2.22/2.48      ((~ (v3_ordinal1 @ sk_A))
% 2.22/2.48         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 2.22/2.48             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['6', '21'])).
% 2.22/2.48  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('24', plain,
% 2.22/2.48      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.22/2.48       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.22/2.48      inference('demod', [status(thm)], ['22', '23'])).
% 2.22/2.48  thf('25', plain,
% 2.22/2.48      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.22/2.48       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.22/2.48      inference('split', [status(esa)], ['8'])).
% 2.22/2.48  thf('26', plain,
% 2.22/2.48      (![X28 : $i, X29 : $i]:
% 2.22/2.48         (~ (v3_ordinal1 @ X28)
% 2.22/2.48          | (r1_ordinal1 @ X29 @ X28)
% 2.22/2.48          | (r2_hidden @ X28 @ X29)
% 2.22/2.48          | ~ (v3_ordinal1 @ X29))),
% 2.22/2.48      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.22/2.48  thf('27', plain,
% 2.22/2.48      (![X26 : $i, X27 : $i]:
% 2.22/2.48         ((r2_hidden @ X26 @ (k1_ordinal1 @ X27)) | ~ (r2_hidden @ X26 @ X27))),
% 2.22/2.48      inference('cnf', [status(esa)], [t13_ordinal1])).
% 2.22/2.48  thf('28', plain,
% 2.22/2.48      (![X0 : $i, X1 : $i]:
% 2.22/2.48         (~ (v3_ordinal1 @ X0)
% 2.22/2.48          | (r1_ordinal1 @ X0 @ X1)
% 2.22/2.48          | ~ (v3_ordinal1 @ X1)
% 2.22/2.48          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 2.22/2.48      inference('sup-', [status(thm)], ['26', '27'])).
% 2.22/2.48  thf('29', plain,
% 2.22/2.48      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('split', [status(esa)], ['0'])).
% 2.22/2.48  thf('30', plain,
% 2.22/2.48      (((~ (v3_ordinal1 @ sk_A)
% 2.22/2.48         | (r1_ordinal1 @ sk_B @ sk_A)
% 2.22/2.48         | ~ (v3_ordinal1 @ sk_B)))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['28', '29'])).
% 2.22/2.48  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('33', plain,
% 2.22/2.48      (((r1_ordinal1 @ sk_B @ sk_A))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.22/2.48  thf('34', plain,
% 2.22/2.48      (![X23 : $i, X24 : $i]:
% 2.22/2.48         (~ (v3_ordinal1 @ X23)
% 2.22/2.48          | ~ (v3_ordinal1 @ X24)
% 2.22/2.48          | (r1_tarski @ X23 @ X24)
% 2.22/2.48          | ~ (r1_ordinal1 @ X23 @ X24))),
% 2.22/2.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.22/2.48  thf('35', plain,
% 2.22/2.48      ((((r1_tarski @ sk_B @ sk_A)
% 2.22/2.48         | ~ (v3_ordinal1 @ sk_A)
% 2.22/2.48         | ~ (v3_ordinal1 @ sk_B)))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('sup-', [status(thm)], ['33', '34'])).
% 2.22/2.48  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('38', plain,
% 2.22/2.48      (((r1_tarski @ sk_B @ sk_A))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.22/2.48  thf('39', plain,
% 2.22/2.48      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('split', [status(esa)], ['8'])).
% 2.22/2.48  thf('40', plain,
% 2.22/2.48      (![X23 : $i, X24 : $i]:
% 2.22/2.48         (~ (v3_ordinal1 @ X23)
% 2.22/2.48          | ~ (v3_ordinal1 @ X24)
% 2.22/2.48          | (r1_tarski @ X23 @ X24)
% 2.22/2.48          | ~ (r1_ordinal1 @ X23 @ X24))),
% 2.22/2.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.22/2.48  thf('41', plain,
% 2.22/2.48      ((((r1_tarski @ sk_A @ sk_B)
% 2.22/2.48         | ~ (v3_ordinal1 @ sk_B)
% 2.22/2.48         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('sup-', [status(thm)], ['39', '40'])).
% 2.22/2.48  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 2.22/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.48  thf('44', plain,
% 2.22/2.48      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.22/2.48  thf('45', plain,
% 2.22/2.48      (![X10 : $i, X12 : $i]:
% 2.22/2.48         (((X10) = (X12))
% 2.22/2.48          | ~ (r1_tarski @ X12 @ X10)
% 2.22/2.48          | ~ (r1_tarski @ X10 @ X12))),
% 2.22/2.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.48  thf('46', plain,
% 2.22/2.48      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 2.22/2.48         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('sup-', [status(thm)], ['44', '45'])).
% 2.22/2.48  thf('47', plain,
% 2.22/2.48      ((((sk_B) = (sk_A)))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 2.22/2.48             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('sup-', [status(thm)], ['38', '46'])).
% 2.22/2.48  thf('48', plain,
% 2.22/2.48      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 2.22/2.48      inference('split', [status(esa)], ['0'])).
% 2.22/2.48  thf('49', plain,
% 2.22/2.48      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 2.22/2.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 2.22/2.48             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 2.22/2.48      inference('sup-', [status(thm)], ['47', '48'])).
% 2.22/2.48  thf('50', plain,
% 2.22/2.48      (![X26 : $i, X27 : $i]:
% 2.22/2.48         ((r2_hidden @ X26 @ (k1_ordinal1 @ X27)) | ((X26) != (X27)))),
% 2.22/2.48      inference('cnf', [status(esa)], [t13_ordinal1])).
% 2.22/2.48  thf('51', plain, (![X27 : $i]: (r2_hidden @ X27 @ (k1_ordinal1 @ X27))),
% 2.22/2.48      inference('simplify', [status(thm)], ['50'])).
% 2.22/2.48  thf('52', plain,
% 2.22/2.48      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 2.22/2.48       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 2.22/2.48      inference('demod', [status(thm)], ['49', '51'])).
% 2.22/2.48  thf('53', plain, ($false),
% 2.22/2.48      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '52'])).
% 2.22/2.48  
% 2.22/2.48  % SZS output end Refutation
% 2.22/2.48  
% 2.22/2.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
