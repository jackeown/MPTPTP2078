%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vLCGLaLjnV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 139 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  631 (1393 expanded)
%              Number of equality atoms :   73 ( 171 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X15 = X16 )
      | ( X15 = X17 )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('6',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','34','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['9','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['11','34'])).

thf('49',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vLCGLaLjnV
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 154 iterations in 0.076s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(d1_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.53       ( ![E:$i]:
% 0.21/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, axiom,
% 0.21/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.21/0.53          | ((X15) = (X16))
% 0.21/0.53          | ((X15) = (X17))
% 0.21/0.53          | ((X15) = (X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l27_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X39 : $i, X40 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ (k1_tarski @ X39) @ X40) | (r2_hidden @ X39 @ X40))),
% 0.21/0.53      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t83_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ X1)
% 0.21/0.53          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t20_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.53         ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ( A ) != ( B ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.53            ( k1_tarski @ A ) ) <=>
% 0.21/0.53          ( ( A ) != ( B ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((((sk_A) = (sk_B))
% 0.21/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53            != (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53          != (k1_tarski @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.53         | (r2_hidden @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((((sk_A) != (sk_B))
% 0.21/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53            = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (~ (((sk_A) = (sk_B))) | 
% 0.21/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['10'])).
% 0.21/0.53  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.53       ( ![E:$i]:
% 0.21/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.53          | (r2_hidden @ X19 @ X23)
% 0.21/0.53          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.53         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.21/0.53          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.21/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.53  thf('14', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['6'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_A)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['10'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_A)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['6'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_B)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X11 : $i, X13 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.21/0.53         | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf(t3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.53          | ~ (r2_hidden @ X4 @ X5)
% 0.21/0.53          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.53          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.53          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.53          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '27'])).
% 0.21/0.53  thf(l24_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X37 : $i, X38 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X37) @ X38) | ~ (r2_hidden @ X37 @ X38))),
% 0.21/0.53      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i, X2 : $i]: (zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53                = (k1_tarski @ sk_A))) & 
% 0.21/0.53             (((sk_A) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.21/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_A))) | 
% 0.21/0.53       ~ (((sk_A) = (sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_A))) | 
% 0.21/0.53       (((sk_A) = (sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['6'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.53          = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['11', '34', '35'])).
% 0.21/0.53  thf('37', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['9', '36'])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(t70_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X24 @ X23)
% 0.21/0.53          | ~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.21/0.53          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.21/0.53         (~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.21/0.53          | ~ (r2_hidden @ X24 @ (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '42'])).
% 0.21/0.53  thf('44', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '44'])).
% 0.21/0.54  thf('46', plain, (((sk_B) = (sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.54  thf('47', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['10'])).
% 0.21/0.54  thf('48', plain, (~ (((sk_A) = (sk_B)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['11', '34'])).
% 0.21/0.54  thf('49', plain, (((sk_A) != (sk_B))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf('50', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
