%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7VuNToAoB

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 5.11s
% Output     : Refutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 264 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  438 (2124 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( r2_hidden @ X23 @ ( k1_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('7',plain,(
    ! [X29: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X29 ) )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('8',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_ordinal1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('10',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X29: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X29 ) )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ( r1_ordinal1 @ X28 @ X27 )
      | ( r2_hidden @ X27 @ X28 )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( r2_hidden @ X25 @ X24 )
      | ~ ( r2_hidden @ X25 @ ( k1_ordinal1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('30',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','20'])).

thf('31',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','20','21'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['37','38'])).

thf(t4_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ D )
        & ( r2_hidden @ D @ A ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ X33 @ X30 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_ordinal1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( sk_B = sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['37','38'])).

thf('45',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['23','46','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7VuNToAoB
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.11/5.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.11/5.32  % Solved by: fo/fo7.sh
% 5.11/5.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.11/5.32  % done 4734 iterations in 4.869s
% 5.11/5.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.11/5.32  % SZS output start Refutation
% 5.11/5.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.11/5.32  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.11/5.32  thf(sk_B_type, type, sk_B: $i).
% 5.11/5.32  thf(sk_A_type, type, sk_A: $i).
% 5.11/5.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.11/5.32  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 5.11/5.32  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 5.11/5.32  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 5.11/5.32  thf(t33_ordinal1, conjecture,
% 5.11/5.32    (![A:$i]:
% 5.11/5.32     ( ( v3_ordinal1 @ A ) =>
% 5.11/5.32       ( ![B:$i]:
% 5.11/5.32         ( ( v3_ordinal1 @ B ) =>
% 5.11/5.32           ( ( r2_hidden @ A @ B ) <=>
% 5.11/5.32             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 5.11/5.32  thf(zf_stmt_0, negated_conjecture,
% 5.11/5.32    (~( ![A:$i]:
% 5.11/5.32        ( ( v3_ordinal1 @ A ) =>
% 5.11/5.32          ( ![B:$i]:
% 5.11/5.32            ( ( v3_ordinal1 @ B ) =>
% 5.11/5.32              ( ( r2_hidden @ A @ B ) <=>
% 5.11/5.32                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 5.11/5.32    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 5.11/5.32  thf('0', plain,
% 5.11/5.32      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('1', plain,
% 5.11/5.32      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.11/5.32      inference('split', [status(esa)], ['0'])).
% 5.11/5.32  thf(t7_ordinal1, axiom,
% 5.11/5.32    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.11/5.32  thf('2', plain,
% 5.11/5.32      (![X34 : $i, X35 : $i]:
% 5.11/5.32         (~ (r2_hidden @ X34 @ X35) | ~ (r1_tarski @ X35 @ X34))),
% 5.11/5.32      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.11/5.32  thf('3', plain,
% 5.11/5.32      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['1', '2'])).
% 5.11/5.32  thf('4', plain,
% 5.11/5.32      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.11/5.32        | ~ (r2_hidden @ sk_A @ sk_B))),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('5', plain,
% 5.11/5.32      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 5.11/5.32       ~ ((r2_hidden @ sk_A @ sk_B))),
% 5.11/5.32      inference('split', [status(esa)], ['4'])).
% 5.11/5.32  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 5.11/5.32  thf('6', plain, (![X23 : $i]: (r2_hidden @ X23 @ (k1_ordinal1 @ X23))),
% 5.11/5.32      inference('cnf', [status(esa)], [t10_ordinal1])).
% 5.11/5.32  thf(t29_ordinal1, axiom,
% 5.11/5.32    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 5.11/5.32  thf('7', plain,
% 5.11/5.32      (![X29 : $i]:
% 5.11/5.32         ((v3_ordinal1 @ (k1_ordinal1 @ X29)) | ~ (v3_ordinal1 @ X29))),
% 5.11/5.32      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.11/5.32  thf('8', plain,
% 5.11/5.32      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('split', [status(esa)], ['0'])).
% 5.11/5.32  thf(redefinition_r1_ordinal1, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 5.11/5.32       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 5.11/5.32  thf('9', plain,
% 5.11/5.32      (![X21 : $i, X22 : $i]:
% 5.11/5.32         (~ (v3_ordinal1 @ X21)
% 5.11/5.32          | ~ (v3_ordinal1 @ X22)
% 5.11/5.32          | (r1_tarski @ X21 @ X22)
% 5.11/5.32          | ~ (r1_ordinal1 @ X21 @ X22))),
% 5.11/5.32      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.11/5.32  thf('10', plain,
% 5.11/5.32      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.11/5.32         | ~ (v3_ordinal1 @ sk_B)
% 5.11/5.32         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['8', '9'])).
% 5.11/5.32  thf('11', plain, ((v3_ordinal1 @ sk_B)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('12', plain,
% 5.11/5.32      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.11/5.32         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('demod', [status(thm)], ['10', '11'])).
% 5.11/5.32  thf('13', plain,
% 5.11/5.32      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['7', '12'])).
% 5.11/5.32  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('15', plain,
% 5.11/5.32      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('demod', [status(thm)], ['13', '14'])).
% 5.11/5.32  thf(d3_tarski, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( r1_tarski @ A @ B ) <=>
% 5.11/5.32       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.11/5.32  thf('16', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.11/5.32         (~ (r2_hidden @ X0 @ X1)
% 5.11/5.32          | (r2_hidden @ X0 @ X2)
% 5.11/5.32          | ~ (r1_tarski @ X1 @ X2))),
% 5.11/5.32      inference('cnf', [status(esa)], [d3_tarski])).
% 5.11/5.32  thf('17', plain,
% 5.11/5.32      ((![X0 : $i]:
% 5.11/5.32          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['15', '16'])).
% 5.11/5.32  thf('18', plain,
% 5.11/5.32      (((r2_hidden @ sk_A @ sk_B))
% 5.11/5.32         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['6', '17'])).
% 5.11/5.32  thf('19', plain,
% 5.11/5.32      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 5.11/5.32      inference('split', [status(esa)], ['4'])).
% 5.11/5.32  thf('20', plain,
% 5.11/5.32      (((r2_hidden @ sk_A @ sk_B)) | 
% 5.11/5.32       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.11/5.32      inference('sup-', [status(thm)], ['18', '19'])).
% 5.11/5.32  thf('21', plain,
% 5.11/5.32      (((r2_hidden @ sk_A @ sk_B)) | 
% 5.11/5.32       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.11/5.32      inference('split', [status(esa)], ['0'])).
% 5.11/5.32  thf('22', plain, (((r2_hidden @ sk_A @ sk_B))),
% 5.11/5.32      inference('sat_resolution*', [status(thm)], ['5', '20', '21'])).
% 5.11/5.32  thf('23', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 5.11/5.32      inference('simpl_trail', [status(thm)], ['3', '22'])).
% 5.11/5.32  thf('24', plain,
% 5.11/5.32      (![X29 : $i]:
% 5.11/5.32         ((v3_ordinal1 @ (k1_ordinal1 @ X29)) | ~ (v3_ordinal1 @ X29))),
% 5.11/5.32      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.11/5.32  thf(t26_ordinal1, axiom,
% 5.11/5.32    (![A:$i]:
% 5.11/5.32     ( ( v3_ordinal1 @ A ) =>
% 5.11/5.32       ( ![B:$i]:
% 5.11/5.32         ( ( v3_ordinal1 @ B ) =>
% 5.11/5.32           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 5.11/5.32  thf('25', plain,
% 5.11/5.32      (![X27 : $i, X28 : $i]:
% 5.11/5.32         (~ (v3_ordinal1 @ X27)
% 5.11/5.32          | (r1_ordinal1 @ X28 @ X27)
% 5.11/5.32          | (r2_hidden @ X27 @ X28)
% 5.11/5.32          | ~ (v3_ordinal1 @ X28))),
% 5.11/5.32      inference('cnf', [status(esa)], [t26_ordinal1])).
% 5.11/5.32  thf(t13_ordinal1, axiom,
% 5.11/5.32    (![A:$i,B:$i]:
% 5.11/5.32     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 5.11/5.32       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 5.11/5.32  thf('26', plain,
% 5.11/5.32      (![X24 : $i, X25 : $i]:
% 5.11/5.32         (((X25) = (X24))
% 5.11/5.32          | (r2_hidden @ X25 @ X24)
% 5.11/5.32          | ~ (r2_hidden @ X25 @ (k1_ordinal1 @ X24)))),
% 5.11/5.32      inference('cnf', [status(esa)], [t13_ordinal1])).
% 5.11/5.32  thf('27', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.11/5.32          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 5.11/5.32          | ~ (v3_ordinal1 @ X1)
% 5.11/5.32          | (r2_hidden @ X1 @ X0)
% 5.11/5.32          | ((X1) = (X0)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['25', '26'])).
% 5.11/5.32  thf('28', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         (~ (v3_ordinal1 @ X0)
% 5.11/5.32          | ((X1) = (X0))
% 5.11/5.32          | (r2_hidden @ X1 @ X0)
% 5.11/5.32          | ~ (v3_ordinal1 @ X1)
% 5.11/5.32          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 5.11/5.32      inference('sup-', [status(thm)], ['24', '27'])).
% 5.11/5.32  thf('29', plain,
% 5.11/5.32      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.11/5.32         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.11/5.32      inference('split', [status(esa)], ['4'])).
% 5.11/5.32  thf('30', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.11/5.32      inference('sat_resolution*', [status(thm)], ['5', '20'])).
% 5.11/5.32  thf('31', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 5.11/5.32      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 5.11/5.32  thf('32', plain,
% 5.11/5.32      ((~ (v3_ordinal1 @ sk_B)
% 5.11/5.32        | (r2_hidden @ sk_B @ sk_A)
% 5.11/5.32        | ((sk_B) = (sk_A))
% 5.11/5.32        | ~ (v3_ordinal1 @ sk_A))),
% 5.11/5.32      inference('sup-', [status(thm)], ['28', '31'])).
% 5.11/5.32  thf('33', plain, ((v3_ordinal1 @ sk_B)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 5.11/5.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.11/5.32  thf('35', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 5.11/5.32      inference('demod', [status(thm)], ['32', '33', '34'])).
% 5.11/5.32  thf('36', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 5.11/5.32      inference('demod', [status(thm)], ['32', '33', '34'])).
% 5.11/5.32  thf('37', plain,
% 5.11/5.32      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.11/5.32      inference('split', [status(esa)], ['0'])).
% 5.11/5.32  thf('38', plain, (((r2_hidden @ sk_A @ sk_B))),
% 5.11/5.32      inference('sat_resolution*', [status(thm)], ['5', '20', '21'])).
% 5.11/5.32  thf('39', plain, ((r2_hidden @ sk_A @ sk_B)),
% 5.11/5.32      inference('simpl_trail', [status(thm)], ['37', '38'])).
% 5.11/5.32  thf(t4_ordinal1, axiom,
% 5.11/5.32    (![A:$i,B:$i,C:$i,D:$i]:
% 5.11/5.32     ( ~( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) & 
% 5.11/5.32          ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ A ) ) ))).
% 5.11/5.32  thf('40', plain,
% 5.11/5.32      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 5.11/5.32         (~ (r2_hidden @ X30 @ X31)
% 5.11/5.32          | ~ (r2_hidden @ X31 @ X32)
% 5.11/5.32          | ~ (r2_hidden @ X33 @ X30)
% 5.11/5.32          | ~ (r2_hidden @ X32 @ X33))),
% 5.11/5.32      inference('cnf', [status(esa)], [t4_ordinal1])).
% 5.11/5.32  thf('41', plain,
% 5.11/5.32      (![X0 : $i, X1 : $i]:
% 5.11/5.32         (~ (r2_hidden @ X1 @ X0)
% 5.11/5.32          | ~ (r2_hidden @ X0 @ sk_A)
% 5.11/5.32          | ~ (r2_hidden @ sk_B @ X1))),
% 5.11/5.32      inference('sup-', [status(thm)], ['39', '40'])).
% 5.11/5.32  thf('42', plain,
% 5.11/5.32      (![X0 : $i]:
% 5.11/5.32         (((sk_B) = (sk_A))
% 5.11/5.32          | ~ (r2_hidden @ sk_B @ X0)
% 5.11/5.32          | ~ (r2_hidden @ X0 @ sk_B))),
% 5.11/5.32      inference('sup-', [status(thm)], ['36', '41'])).
% 5.11/5.32  thf('43', plain,
% 5.11/5.32      ((((sk_B) = (sk_A)) | ~ (r2_hidden @ sk_A @ sk_B) | ((sk_B) = (sk_A)))),
% 5.11/5.32      inference('sup-', [status(thm)], ['35', '42'])).
% 5.11/5.32  thf('44', plain, ((r2_hidden @ sk_A @ sk_B)),
% 5.11/5.32      inference('simpl_trail', [status(thm)], ['37', '38'])).
% 5.11/5.32  thf('45', plain, ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 5.11/5.32      inference('demod', [status(thm)], ['43', '44'])).
% 5.11/5.32  thf('46', plain, (((sk_B) = (sk_A))),
% 5.11/5.32      inference('simplify', [status(thm)], ['45'])).
% 5.11/5.32  thf('47', plain,
% 5.11/5.32      (![X1 : $i, X3 : $i]:
% 5.11/5.32         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.11/5.32      inference('cnf', [status(esa)], [d3_tarski])).
% 5.11/5.32  thf('48', plain,
% 5.11/5.32      (![X1 : $i, X3 : $i]:
% 5.11/5.32         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.11/5.32      inference('cnf', [status(esa)], [d3_tarski])).
% 5.11/5.32  thf('49', plain,
% 5.11/5.32      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 5.11/5.32      inference('sup-', [status(thm)], ['47', '48'])).
% 5.11/5.32  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.11/5.32      inference('simplify', [status(thm)], ['49'])).
% 5.11/5.32  thf('51', plain, ($false),
% 5.11/5.32      inference('demod', [status(thm)], ['23', '46', '50'])).
% 5.11/5.32  
% 5.11/5.32  % SZS output end Refutation
% 5.11/5.32  
% 5.11/5.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
