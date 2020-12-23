%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coKXCuoQpJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 132 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  467 (1091 expanded)
%              Number of equality atoms :   43 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ ( k11_relat_1 @ X50 @ X51 ) )
      | ( r2_hidden @ ( k4_tarski @ X51 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 )
      | ( r2_hidden @ X42 @ X45 )
      | ( X45
       != ( k1_relat_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ ( k1_relat_1 @ X44 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('12',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ X45 )
      | ( r2_hidden @ ( k4_tarski @ X46 @ ( sk_D_1 @ X46 @ X44 ) ) @ X44 )
      | ( X45
       != ( k1_relat_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X46 @ ( sk_D_1 @ X46 @ X44 ) ) @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X51 @ X49 ) @ X50 )
      | ( r2_hidden @ X49 @ ( k11_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('23',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('25',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['9','32','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['7','34'])).

thf('36',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('40',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','32'])).

thf('41',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coKXCuoQpJ
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:04:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 147 iterations in 0.052s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(t7_xboole_0, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.50  thf(t204_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ C ) =>
% 0.19/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.50         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X49 @ (k11_relat_1 @ X50 @ X51))
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ X51 @ X49) @ X50)
% 0.19/0.50          | ~ (v1_relat_1 @ X50))),
% 0.19/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.19/0.50             X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(d4_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.50       ( ![C:$i]:
% 0.19/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.19/0.50         (~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44)
% 0.19/0.50          | (r2_hidden @ X42 @ X45)
% 0.19/0.50          | ((X45) != (k1_relat_1 @ X44)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.19/0.50         ((r2_hidden @ X42 @ (k1_relat_1 @ X44))
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44))),
% 0.19/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X0)
% 0.19/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.50  thf(t205_relat_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( v1_relat_1 @ B ) =>
% 0.19/0.50          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.50            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.19/0.50        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.50      inference('split', [status(esa)], ['6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.19/0.50        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.50      inference('split', [status(esa)], ['8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('split', [status(esa)], ['6'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.50      inference('split', [status(esa)], ['8'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X46 @ X45)
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ X46 @ (sk_D_1 @ X46 @ X44)) @ X44)
% 0.19/0.50          | ((X45) != (k1_relat_1 @ X44)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X44 : $i, X46 : $i]:
% 0.19/0.50         ((r2_hidden @ (k4_tarski @ X46 @ (sk_D_1 @ X46 @ X44)) @ X44)
% 0.19/0.50          | ~ (r2_hidden @ X46 @ (k1_relat_1 @ X44)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.19/0.50         (~ (r2_hidden @ (k4_tarski @ X51 @ X49) @ X50)
% 0.19/0.50          | (r2_hidden @ X49 @ (k11_relat_1 @ X50 @ X51))
% 0.19/0.50          | ~ (v1_relat_1 @ X50))),
% 0.19/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.50         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.50            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.50  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.19/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.50             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['10', '18'])).
% 0.19/0.50  thf(l1_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X34 : $i, X36 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.19/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (((r1_tarski @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) @ k1_xboole_0))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.50             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.50  thf(t3_xboole_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.50             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf(t20_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.50         ( k1_tarski @ A ) ) <=>
% 0.19/0.50       ( ( A ) != ( B ) ) ))).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X37 : $i, X38 : $i]:
% 0.19/0.50         (((X38) != (X37))
% 0.19/0.50          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.19/0.50              != (k1_tarski @ X38)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X37 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.19/0.50           != (k1_tarski @ X37))),
% 0.19/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.50  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.50  thf(t100_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ X2 @ X3)
% 0.19/0.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf(t92_xboole_1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('29', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.50  thf('30', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.19/0.50      inference('demod', [status(thm)], ['25', '28', '29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.19/0.50             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['23', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.19/0.50       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.19/0.50       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('split', [status(esa)], ['6'])).
% 0.19/0.50  thf('34', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['9', '32', '33'])).
% 0.19/0.50  thf('35', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['7', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.19/0.50        | ~ (v1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '35'])).
% 0.19/0.50  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('38', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.19/0.50         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('split', [status(esa)], ['8'])).
% 0.19/0.50  thf('40', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['9', '32'])).
% 0.19/0.50  thf('41', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
