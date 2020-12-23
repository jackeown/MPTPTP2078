%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ADESKfFLzz

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 132 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  436 (1102 expanded)
%              Number of equality atoms :   39 (  99 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('15',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('26',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','22','26'])).

thf('28',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('42',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['35','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['24','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ADESKfFLzz
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 64 iterations in 0.031s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(t95_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.21/0.48        | ((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.21/0.48         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.21/0.48       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(dt_k7_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.48  thf(t90_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.48         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k7_relat_1 @ X12 @ X13))
% 0.21/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13))
% 0.21/0.48          | ~ (v1_relat_1 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.21/0.48        | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf(t7_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.48  thf(t4_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B_1)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '10'])).
% 0.21/0.48  thf('12', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A)) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf(t64_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.21/0.48          | ((X11) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.48         | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '16'])).
% 0.21/0.48  thf('18', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.48             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '22'])).
% 0.21/0.48  thf('24', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf('27', plain, ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '22', '26'])).
% 0.21/0.48  thf('28', plain, (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k7_relat_1 @ X12 @ X13))
% 0.21/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13))
% 0.21/0.48          | ~ (v1_relat_1 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X1 @ X2)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.21/0.48           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B_1)) @ 
% 0.21/0.48         (k1_relat_1 @ k1_xboole_0))
% 0.21/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['28', '31'])).
% 0.21/0.48  thf(t60_relat_1, axiom,
% 0.21/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B_1)) @ k1_xboole_0)
% 0.21/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.48  thf('36', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.48  thf('42', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['35', '42'])).
% 0.21/0.48  thf('44', plain, ($false), inference('demod', [status(thm)], ['24', '43'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
