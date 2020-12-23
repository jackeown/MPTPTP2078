%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GnM67NRhMq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 111 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  453 ( 905 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('2',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X14 @ X15 )
      | ( r1_ordinal1 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_ordinal1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('24',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','26'])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('31',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r2_hidden @ X23 @ X22 )
      | ( X23 = X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('43',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ( X20 != X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('49',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_ordinal1 @ X21 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','49'])).

thf('51',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GnM67NRhMq
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 271 iterations in 0.136s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.56  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(t34_ordinal1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.56           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.56             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.56              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.56                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.56        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('2', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(connectedness_r1_ordinal1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.56       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X14)
% 0.37/0.56          | ~ (v3_ordinal1 @ X15)
% 0.37/0.56          | (r1_ordinal1 @ X14 @ X15)
% 0.37/0.56          | (r1_ordinal1 @ X15 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_ordinal1 @ X0 @ sk_A)
% 0.37/0.56          | (r1_ordinal1 @ sk_A @ X0)
% 0.37/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.56       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X17)
% 0.37/0.56          | ~ (v3_ordinal1 @ X18)
% 0.37/0.56          | (r1_tarski @ X17 @ X18)
% 0.37/0.56          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X0)
% 0.37/0.56          | (r1_ordinal1 @ sk_A @ X0)
% 0.37/0.56          | (r1_tarski @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X0)
% 0.37/0.56          | (r1_ordinal1 @ sk_A @ X0)
% 0.37/0.56          | (r1_tarski @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ sk_A)
% 0.37/0.56          | (r1_ordinal1 @ sk_A @ X0)
% 0.37/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['10'])).
% 0.37/0.56  thf(t13_ordinal1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.56       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (((X20) = (X19))
% 0.37/0.56          | (r2_hidden @ X20 @ X19)
% 0.37/0.56          | ~ (r2_hidden @ X20 @ (k1_ordinal1 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf(t7_ordinal1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X24 : $i, X25 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (((~ (v3_ordinal1 @ sk_B)
% 0.37/0.56         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.56         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '15'])).
% 0.37/0.56  thf('17', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      ((((sk_A) = (sk_B)))
% 0.37/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.37/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.37/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.37/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_ordinal1 @ X0 @ sk_A)
% 0.37/0.56          | (r1_ordinal1 @ sk_A @ X0)
% 0.37/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('24', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.37/0.56      inference('eq_fact', [status(thm)], ['23'])).
% 0.37/0.56  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('26', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.56       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['10'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['10'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X17)
% 0.37/0.56          | ~ (v3_ordinal1 @ X18)
% 0.37/0.56          | (r1_tarski @ X17 @ X18)
% 0.37/0.56          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      ((((r1_tarski @ sk_A @ sk_B)
% 0.37/0.56         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.56         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.56  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.37/0.56  thf(t24_ordinal1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.56           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.37/0.56                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X22)
% 0.37/0.56          | (r2_hidden @ X23 @ X22)
% 0.37/0.56          | ((X23) = (X22))
% 0.37/0.56          | (r2_hidden @ X22 @ X23)
% 0.37/0.56          | ~ (v3_ordinal1 @ X23))),
% 0.37/0.56      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X24 : $i, X25 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v3_ordinal1 @ X1)
% 0.37/0.56          | (r2_hidden @ X0 @ X1)
% 0.37/0.56          | ((X1) = (X0))
% 0.37/0.56          | ~ (v3_ordinal1 @ X0)
% 0.37/0.56          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (((~ (v3_ordinal1 @ sk_A)
% 0.37/0.56         | ((sk_B) = (sk_A))
% 0.37/0.56         | (r2_hidden @ sk_A @ sk_B)
% 0.37/0.56         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['34', '37'])).
% 0.37/0.56  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ~ (r2_hidden @ X20 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.37/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((((sk_B) = (sk_A)))
% 0.37/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.37/0.56             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.37/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.37/0.56             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ((X20) != (X21)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.56  thf('49', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_ordinal1 @ X21))),
% 0.37/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.37/0.56       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '49'])).
% 0.37/0.56  thf('51', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '50'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
