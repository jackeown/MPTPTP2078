%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n6qoX8UE92

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:11 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 456 expanded)
%              Number of leaves         :   24 ( 116 expanded)
%              Depth                    :   24
%              Number of atoms          :  584 (3681 expanded)
%              Number of equality atoms :   67 ( 538 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('2',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('8',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('12',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['8','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['7','14'])).

thf('16',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('18',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','18','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['3','22'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['7','14'])).

thf('31',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['7','14'])).

thf('39',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('40',plain,(
    ! [X53: $i,X55: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X53 ) @ X55 )
      | ~ ( r2_hidden @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('46',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ~ ( zip_tseitin_0 @ ( sk_B @ sk_A ) @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,
    ( ( ( sk_B @ sk_A )
      = sk_B_1 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['3','22'])).

thf('56',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference(simplify,[status(thm)],['53'])).

thf('57',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','54','55','56'])).

thf('58',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['21','60'])).

thf('62',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['59','61'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n6qoX8UE92
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.54  % Solved by: fo/fo7.sh
% 0.34/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.54  % done 172 iterations in 0.078s
% 0.34/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.54  % SZS output start Refutation
% 0.34/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.34/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.34/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.54  thf(t7_xboole_0, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.34/0.54  thf('0', plain,
% 0.34/0.54      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.34/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.54  thf('1', plain,
% 0.34/0.54      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.34/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.54  thf(t39_zfmisc_1, conjecture,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.34/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.54    (~( ![A:$i,B:$i]:
% 0.34/0.54        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.34/0.54          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.34/0.54    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.34/0.54  thf('2', plain,
% 0.34/0.54      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.34/0.54        | ((sk_A) = (k1_xboole_0))
% 0.34/0.54        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('3', plain,
% 0.34/0.54      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('split', [status(esa)], ['2'])).
% 0.34/0.54  thf('4', plain,
% 0.34/0.54      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('5', plain,
% 0.34/0.54      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('split', [status(esa)], ['4'])).
% 0.34/0.54  thf('6', plain,
% 0.34/0.54      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.34/0.54        | ((sk_A) = (k1_xboole_0))
% 0.34/0.54        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('7', plain,
% 0.34/0.54      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.34/0.54      inference('split', [status(esa)], ['4'])).
% 0.34/0.54  thf('8', plain,
% 0.34/0.54      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.34/0.54       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('split', [status(esa)], ['4'])).
% 0.34/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.54  thf('9', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.34/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.54  thf('10', plain,
% 0.34/0.54      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.34/0.54      inference('split', [status(esa)], ['2'])).
% 0.34/0.54  thf('11', plain,
% 0.34/0.54      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('split', [status(esa)], ['4'])).
% 0.34/0.54  thf('12', plain,
% 0.34/0.54      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) & 
% 0.34/0.54             (((sk_A) = (k1_xboole_0))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.54  thf('13', plain,
% 0.34/0.54      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) | 
% 0.34/0.54       ~ (((sk_A) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['9', '12'])).
% 0.34/0.54  thf('14', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['8', '13'])).
% 0.34/0.54  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['7', '14'])).
% 0.34/0.54  thf('16', plain,
% 0.34/0.54      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.34/0.54        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['6', '15'])).
% 0.34/0.54  thf('17', plain,
% 0.34/0.54      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('split', [status(esa)], ['4'])).
% 0.34/0.54  thf('18', plain,
% 0.34/0.54      ((((sk_A) = (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.54  thf(d10_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.54  thf('19', plain,
% 0.34/0.54      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.34/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.54  thf('20', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.34/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.34/0.54  thf('21', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('demod', [status(thm)], ['5', '18', '20'])).
% 0.34/0.54  thf('22', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['21'])).
% 0.34/0.54  thf('23', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['3', '22'])).
% 0.34/0.54  thf(t28_xboole_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.34/0.54  thf('24', plain,
% 0.34/0.54      (![X10 : $i, X11 : $i]:
% 0.34/0.54         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.34/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.34/0.54  thf('25', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.34/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.54  thf(d4_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i]:
% 0.34/0.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.34/0.54       ( ![D:$i]:
% 0.34/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.34/0.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.34/0.54  thf('26', plain,
% 0.34/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.34/0.54          | (r2_hidden @ X4 @ X2)
% 0.34/0.54          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.34/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.34/0.54  thf('27', plain,
% 0.34/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.34/0.54         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.34/0.54  thf('28', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.34/0.54  thf('29', plain,
% 0.34/0.54      ((((sk_A) = (k1_xboole_0))
% 0.34/0.54        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['1', '28'])).
% 0.34/0.54  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['7', '14'])).
% 0.34/0.54  thf('31', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.34/0.54  thf('32', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.34/0.54          | ~ (r2_hidden @ X0 @ X2)
% 0.34/0.54          | (r2_hidden @ X0 @ X3)
% 0.34/0.54          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.34/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.34/0.54  thf('33', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.34/0.54          | ~ (r2_hidden @ X0 @ X2)
% 0.34/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.34/0.54  thf('34', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (r2_hidden @ (sk_B @ sk_A) @ X0)
% 0.34/0.54          | (r2_hidden @ (sk_B @ sk_A) @ 
% 0.34/0.54             (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['31', '33'])).
% 0.34/0.54  thf('35', plain,
% 0.34/0.54      ((((sk_A) = (k1_xboole_0))
% 0.34/0.54        | (r2_hidden @ (sk_B @ sk_A) @ 
% 0.34/0.54           (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['0', '34'])).
% 0.34/0.54  thf('36', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.34/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.54  thf('37', plain,
% 0.34/0.54      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_A) @ sk_A))),
% 0.34/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.34/0.54  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['7', '14'])).
% 0.34/0.54  thf('39', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.34/0.54  thf(l1_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.34/0.54  thf('40', plain,
% 0.34/0.54      (![X53 : $i, X55 : $i]:
% 0.34/0.54         ((r1_tarski @ (k1_tarski @ X53) @ X55) | ~ (r2_hidden @ X53 @ X55))),
% 0.34/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.34/0.54  thf('41', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A)),
% 0.34/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.54  thf('42', plain,
% 0.34/0.54      (![X7 : $i, X9 : $i]:
% 0.34/0.54         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.34/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.54  thf('43', plain,
% 0.34/0.54      ((~ (r1_tarski @ sk_A @ (k1_tarski @ (sk_B @ sk_A)))
% 0.34/0.54        | ((sk_A) = (k1_tarski @ (sk_B @ sk_A))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.34/0.54  thf(d1_enumset1, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.34/0.54       ( ![E:$i]:
% 0.34/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.34/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_1, axiom,
% 0.34/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.34/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.34/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.34/0.54  thf('44', plain,
% 0.34/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.34/0.54         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.34/0.54          | ((X14) = (X15))
% 0.34/0.54          | ((X14) = (X16))
% 0.34/0.54          | ((X14) = (X17)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.54  thf('45', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.34/0.54  thf(t69_enumset1, axiom,
% 0.34/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.54  thf('46', plain,
% 0.34/0.54      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf(t70_enumset1, axiom,
% 0.34/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.34/0.54  thf('47', plain,
% 0.34/0.54      (![X26 : $i, X27 : $i]:
% 0.34/0.54         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.34/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.34/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.34/0.54  thf(zf_stmt_3, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.34/0.54       ( ![E:$i]:
% 0.34/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.34/0.54  thf('48', plain,
% 0.34/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X23 @ X22)
% 0.34/0.54          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 0.34/0.54          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.54  thf('49', plain,
% 0.34/0.54      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.34/0.54         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 0.34/0.54          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.34/0.54  thf('50', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.34/0.54          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['47', '49'])).
% 0.34/0.54  thf('51', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.34/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['46', '50'])).
% 0.34/0.54  thf('52', plain,
% 0.34/0.54      (~ (zip_tseitin_0 @ (sk_B @ sk_A) @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.34/0.54      inference('sup-', [status(thm)], ['45', '51'])).
% 0.34/0.54  thf('53', plain,
% 0.34/0.54      ((((sk_B @ sk_A) = (sk_B_1))
% 0.34/0.54        | ((sk_B @ sk_A) = (sk_B_1))
% 0.34/0.54        | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['44', '52'])).
% 0.34/0.54  thf('54', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.34/0.54  thf('55', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['3', '22'])).
% 0.34/0.54  thf('56', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.34/0.54  thf('57', plain, (((sk_A) = (k1_tarski @ sk_B_1))),
% 0.34/0.54      inference('demod', [status(thm)], ['43', '54', '55', '56'])).
% 0.34/0.54  thf('58', plain,
% 0.34/0.54      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.34/0.54        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('59', plain,
% 0.34/0.54      ((((sk_A) != (k1_tarski @ sk_B_1)))
% 0.34/0.54         <= (~ (((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.34/0.54      inference('split', [status(esa)], ['58'])).
% 0.34/0.54  thf('60', plain,
% 0.34/0.54      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 0.34/0.54       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('split', [status(esa)], ['58'])).
% 0.34/0.54  thf('61', plain, (~ (((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['21', '60'])).
% 0.34/0.54  thf('62', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['59', '61'])).
% 0.34/0.54  thf('63', plain, ($false),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['57', '62'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.34/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
