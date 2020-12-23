%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yqCAuuRm3F

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  363 ( 616 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X52: $i] :
      ( ( v1_funct_1 @ X52 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X48: $i] :
      ( ( v1_relat_1 @ X48 )
      | ( r2_hidden @ ( sk_B @ X48 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != X42 )
      | ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X41 @ ( k1_tarski @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ~ ( r2_hidden @ X42 @ ( k4_xboole_0 @ X41 @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','11'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X51: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X51 ) )
      | ~ ( v1_xboole_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ~ ( v1_funct_1 @ X53 )
      | ( r2_hidden @ ( sk_C_1 @ X53 @ X54 ) @ ( k1_relat_1 @ X53 ) )
      | ( v5_funct_1 @ X53 @ X54 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('22',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','26'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('33',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v5_funct_1 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','26'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yqCAuuRm3F
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:51:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.56  % Solved by: fo/fo7.sh
% 0.19/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.56  % done 322 iterations in 0.118s
% 0.19/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.56  % SZS output start Refutation
% 0.19/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.56  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.19/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.56  thf(cc1_funct_1, axiom,
% 0.19/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.19/0.56  thf('0', plain, (![X52 : $i]: ((v1_funct_1 @ X52) | ~ (v1_xboole_0 @ X52))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.19/0.56  thf(d1_relat_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.56              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.56  thf('1', plain,
% 0.19/0.56      (![X48 : $i]: ((v1_relat_1 @ X48) | (r2_hidden @ (sk_B @ X48) @ X48))),
% 0.19/0.56      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.56  thf('2', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.56  thf(t100_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.56  thf('3', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.19/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.56  thf('4', plain,
% 0.19/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.56  thf(t69_enumset1, axiom,
% 0.19/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.56  thf('5', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.19/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.56  thf(t64_zfmisc_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.19/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.19/0.56  thf('6', plain,
% 0.19/0.56      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.19/0.56         (((X40) != (X42))
% 0.19/0.56          | ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X41 @ (k1_tarski @ X42))))),
% 0.19/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.19/0.56  thf('7', plain,
% 0.19/0.56      (![X41 : $i, X42 : $i]:
% 0.19/0.56         ~ (r2_hidden @ X42 @ (k4_xboole_0 @ X41 @ (k1_tarski @ X42)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.56  thf('8', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.19/0.56  thf('9', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ~ (r2_hidden @ X0 @ 
% 0.19/0.56            (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['4', '8'])).
% 0.19/0.56  thf(t92_xboole_1, axiom,
% 0.19/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.56  thf('10', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.19/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.56  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.56  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.56      inference('sup-', [status(thm)], ['1', '11'])).
% 0.19/0.56  thf(fc10_relat_1, axiom,
% 0.19/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.19/0.56  thf('13', plain,
% 0.19/0.56      (![X51 : $i]:
% 0.19/0.56         ((v1_xboole_0 @ (k1_relat_1 @ X51)) | ~ (v1_xboole_0 @ X51))),
% 0.19/0.56      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.19/0.56  thf(d20_funct_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.56           ( ( v5_funct_1 @ B @ A ) <=>
% 0.19/0.56             ( ![C:$i]:
% 0.19/0.56               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.56                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('14', plain,
% 0.19/0.56      (![X53 : $i, X54 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X53)
% 0.19/0.56          | ~ (v1_funct_1 @ X53)
% 0.19/0.56          | (r2_hidden @ (sk_C_1 @ X53 @ X54) @ (k1_relat_1 @ X53))
% 0.19/0.56          | (v5_funct_1 @ X53 @ X54)
% 0.19/0.56          | ~ (v1_funct_1 @ X54)
% 0.19/0.56          | ~ (v1_relat_1 @ X54))),
% 0.19/0.56      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.19/0.56  thf(l13_xboole_0, axiom,
% 0.19/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.56  thf('15', plain,
% 0.19/0.56      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.56  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.56  thf('17', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.56  thf('18', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | (v5_funct_1 @ X0 @ X1)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.56  thf('19', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         (~ (v1_xboole_0 @ X0)
% 0.19/0.56          | ~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | (v5_funct_1 @ X0 @ X1)
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1))),
% 0.19/0.56      inference('sup-', [status(thm)], ['13', '18'])).
% 0.19/0.56  thf('20', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.56          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['12', '19'])).
% 0.19/0.56  thf(t66_xboole_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.56       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.56  thf('21', plain,
% 0.19/0.56      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.56  thf('22', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.56  thf(t69_xboole_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.19/0.56  thf('23', plain,
% 0.19/0.56      (![X9 : $i, X10 : $i]:
% 0.19/0.56         (~ (r1_xboole_0 @ X9 @ X10)
% 0.19/0.56          | ~ (r1_tarski @ X9 @ X10)
% 0.19/0.56          | (v1_xboole_0 @ X9))),
% 0.19/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.19/0.56  thf('24', plain,
% 0.19/0.56      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.56  thf(d10_xboole_0, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.56  thf('25', plain,
% 0.19/0.56      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.19/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.56  thf('26', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.19/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.56  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['24', '26'])).
% 0.19/0.56  thf('28', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['20', '27'])).
% 0.19/0.56  thf('29', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.56          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ~ (v1_relat_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['0', '28'])).
% 0.19/0.56  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['24', '26'])).
% 0.19/0.56  thf('31', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ~ (v1_relat_1 @ X0))),
% 0.19/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.56  thf('32', plain,
% 0.19/0.56      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.56  thf(t174_funct_1, conjecture,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.56       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.19/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.56    (~( ![A:$i]:
% 0.19/0.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.56          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.19/0.56    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.19/0.56  thf('33', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('34', plain,
% 0.19/0.56      (![X0 : $i]: (~ (v5_funct_1 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.56  thf('35', plain,
% 0.19/0.56      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.56        | ~ (v1_funct_1 @ sk_A)
% 0.19/0.56        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['31', '34'])).
% 0.19/0.56  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('37', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.56      inference('demod', [status(thm)], ['24', '26'])).
% 0.19/0.56  thf('39', plain, ($false),
% 0.19/0.56      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.19/0.56  
% 0.19/0.56  % SZS output end Refutation
% 0.19/0.56  
% 0.19/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
