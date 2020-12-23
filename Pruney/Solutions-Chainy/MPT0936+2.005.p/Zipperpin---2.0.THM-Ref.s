%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5SnhtOtTlQ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:23 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 141 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  552 (1197 expanded)
%              Number of equality atoms :   71 ( 131 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) )
        = X40 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k3_mcart_1 @ X44 @ X45 @ X46 )
      = ( k4_tarski @ ( k4_tarski @ X44 @ X45 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
        = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('10',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X32 @ X37 )
      | ( X37
       != ( k2_enumset1 @ X36 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X32 @ ( k2_enumset1 @ X36 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X30 @ X26 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('35',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('39',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5SnhtOtTlQ
% 0.12/0.35  % Computer   : n011.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 14:40:42 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 157 iterations in 0.219s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(t69_enumset1, axiom,
% 0.45/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.68  thf('0', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(t36_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.45/0.68         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.45/0.68       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.45/0.68         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24))
% 0.45/0.68           = (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X22 @ X24)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.45/0.68           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf('3', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.45/0.68           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf(t195_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.45/0.68               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X40 : $i, X41 : $i]:
% 0.45/0.68         (((X40) = (k1_xboole_0))
% 0.45/0.68          | ((k1_relat_1 @ (k2_zfmisc_1 @ X40 @ X41)) = (X40))
% 0.45/0.68          | ((X41) = (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.68            = (k1_tarski @ X1))
% 0.45/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.68          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf(d3_mcart_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.68         ((k3_mcart_1 @ X44 @ X45 @ X46)
% 0.45/0.68           = (k4_tarski @ (k4_tarski @ X44 @ X45) @ X46))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.68            = (k1_tarski @ X1))
% 0.45/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.68          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.45/0.68            = (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.45/0.68          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0))
% 0.45/0.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.68  thf(t97_mcart_1, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k1_relat_1 @
% 0.45/0.68         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.45/0.68       ( k1_tarski @ A ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.68        ( ( k1_relat_1 @
% 0.45/0.68            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.45/0.68          ( k1_tarski @ A ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (((k1_relat_1 @ 
% 0.45/0.68         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.45/0.68         != (k1_tarski @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      ((((k1_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.45/0.68          != (k1_tarski @ sk_A))
% 0.45/0.68        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.45/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['6', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.68  thf(t70_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf('15', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf(t71_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.68  thf(d2_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.68     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.45/0.68       ( ![F:$i]:
% 0.45/0.68         ( ( r2_hidden @ F @ E ) <=>
% 0.45/0.68           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.45/0.68                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_2, axiom,
% 0.45/0.68    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.45/0.68     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.45/0.68       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.45/0.68         ( ( F ) != ( D ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_3, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.68     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.45/0.68       ( ![F:$i]:
% 0.45/0.68         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.45/0.68          | (r2_hidden @ X32 @ X37)
% 0.45/0.68          | ((X37) != (k2_enumset1 @ X36 @ X35 @ X34 @ X33)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.68         ((r2_hidden @ X32 @ (k2_enumset1 @ X36 @ X35 @ X34 @ X33))
% 0.45/0.68          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.45/0.68      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.45/0.68          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.45/0.68      inference('sup+', [status(thm)], ['17', '19'])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.68         (((X27) != (X26)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.68         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X30 @ X26)),
% 0.45/0.68      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.45/0.68      inference('sup-', [status(thm)], ['20', '22'])).
% 0.45/0.68  thf(t7_ordinal1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (![X42 : $i, X43 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X42 @ X43) | ~ (r1_tarski @ X43 @ X42))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X2)),
% 0.45/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.68  thf('26', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '25'])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      ((~ (r1_tarski @ k1_xboole_0 @ (k4_tarski @ sk_A @ sk_B))
% 0.45/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '26'])).
% 0.45/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.68  thf('28', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.68  thf('30', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '25'])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      ((~ (r1_tarski @ k1_xboole_0 @ sk_C)
% 0.45/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.68  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.68  thf('34', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '25'])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      ((~ (r1_tarski @ k1_xboole_0 @ sk_B)
% 0.45/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.68  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.68      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.68  thf('38', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '25'])).
% 0.45/0.68  thf('39', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.68  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.68  thf('41', plain, ($false), inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
