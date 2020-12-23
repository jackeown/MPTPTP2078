%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ek5Uj7unq2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:48 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  497 ( 723 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('32',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['9','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ek5Uj7unq2
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 703 iterations in 0.353s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.81  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.81  thf(t45_zfmisc_1, conjecture,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.58/0.81       ( r2_hidden @ A @ B ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i,B:$i]:
% 0.58/0.81        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.58/0.81          ( r2_hidden @ A @ B ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.58/0.81  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(t69_enumset1, axiom,
% 0.58/0.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.81  thf('1', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf(t70_enumset1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.81  thf('2', plain,
% 0.58/0.81      (![X36 : $i, X37 : $i]:
% 0.58/0.81         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.58/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.81  thf(d1_enumset1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.81       ( ![E:$i]:
% 0.58/0.81         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.81           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.81  thf(zf_stmt_2, axiom,
% 0.58/0.81    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.81     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.81       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_3, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.81       ( ![E:$i]:
% 0.58/0.81         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.81         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.58/0.81          | (r2_hidden @ X28 @ X32)
% 0.58/0.81          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.81         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 0.58/0.81          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 0.58/0.81      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.81          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['2', '4'])).
% 0.58/0.81  thf('6', plain,
% 0.58/0.81      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.81         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.81  thf('7', plain,
% 0.58/0.81      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.58/0.81         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 0.58/0.81      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.81  thf('8', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['5', '7'])).
% 0.58/0.81  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['1', '8'])).
% 0.58/0.81  thf('10', plain,
% 0.58/0.81      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.81         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.58/0.81          | ((X24) = (X25))
% 0.58/0.81          | ((X24) = (X26))
% 0.58/0.81          | ((X24) = (X27)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.81  thf(d3_tarski, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X3 : $i, X5 : $i]:
% 0.58/0.81         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf('13', plain,
% 0.58/0.81      (![X36 : $i, X37 : $i]:
% 0.58/0.81         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.58/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X33 @ X32)
% 0.58/0.81          | ~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.58/0.81          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.81  thf('15', plain,
% 0.58/0.81      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.58/0.81         (~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.58/0.81          | ~ (r2_hidden @ X33 @ (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['13', '15'])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.58/0.81          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['12', '16'])).
% 0.58/0.81  thf('18', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.58/0.81          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['11', '17'])).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.58/0.81          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.58/0.81          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.58/0.81          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['10', '18'])).
% 0.58/0.81  thf('20', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.58/0.81          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.81  thf('21', plain,
% 0.58/0.81      (![X3 : $i, X5 : $i]:
% 0.58/0.81         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('22', plain,
% 0.58/0.81      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(d10_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      (![X8 : $i, X10 : $i]:
% 0.58/0.81         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('24', plain,
% 0.58/0.81      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.58/0.81        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.81  thf(commutativity_k2_tarski, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.81  thf('25', plain,
% 0.58/0.81      (![X21 : $i, X22 : $i]:
% 0.58/0.81         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.81  thf(l51_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.81  thf('26', plain,
% 0.58/0.81      (![X63 : $i, X64 : $i]:
% 0.58/0.81         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.58/0.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.81  thf('27', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['25', '26'])).
% 0.58/0.81  thf('28', plain,
% 0.58/0.81      (![X63 : $i, X64 : $i]:
% 0.58/0.81         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.58/0.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.81  thf('29', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.81  thf(t7_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.81  thf('30', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.81  thf('32', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['24', '29', '30', '31'])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.81  thf('34', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.81  thf('35', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['33', '34'])).
% 0.58/0.81  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.58/0.81      inference('sup+', [status(thm)], ['32', '35'])).
% 0.58/0.81  thf('37', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X2 @ X3)
% 0.58/0.81          | (r2_hidden @ X2 @ X4)
% 0.58/0.81          | ~ (r1_tarski @ X3 @ X4))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('38', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.58/0.81          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.58/0.81      inference('sup-', [status(thm)], ['21', '38'])).
% 0.58/0.81  thf('40', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ sk_A @ sk_B)
% 0.58/0.81          | (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.58/0.81          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['20', '39'])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r2_hidden @ sk_A @ sk_B))),
% 0.58/0.81      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.81  thf('42', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('43', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.58/0.81      inference('clc', [status(thm)], ['41', '42'])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X2 @ X3)
% 0.58/0.81          | (r2_hidden @ X2 @ X4)
% 0.58/0.81          | ~ (r1_tarski @ X3 @ X4))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('45', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['43', '44'])).
% 0.58/0.81  thf('46', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.58/0.81      inference('sup-', [status(thm)], ['9', '45'])).
% 0.58/0.81  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
