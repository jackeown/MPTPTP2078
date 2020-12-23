%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ic5N3YZd0m

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 328 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  542 (2686 expanded)
%              Number of equality atoms :   67 ( 397 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ~ ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_A )
    | ( ( sk_B @ sk_B_1 )
      = sk_A )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['11','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['11','34'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference(demod,[status(thm)],['6','35','36'])).

thf('38',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['11','34'])).

thf('48',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['11','34'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('57',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['11','34'])).

thf('59',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['39','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ic5N3YZd0m
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.61  % Solved by: fo/fo7.sh
% 0.22/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.61  % done 290 iterations in 0.141s
% 0.22/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.61  % SZS output start Refutation
% 0.22/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.61  thf(t44_zfmisc_1, conjecture,
% 0.22/0.61    (![A:$i,B:$i,C:$i]:
% 0.22/0.61     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.61          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.61          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.61        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.61             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.61             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.61    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.22/0.61  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.61  thf('1', plain,
% 0.22/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.61  thf(t7_xboole_1, axiom,
% 0.22/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.61  thf('2', plain,
% 0.22/0.61      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.22/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.61  thf('3', plain,
% 0.22/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.61  thf('4', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('sup+', [status(thm)], ['0', '3'])).
% 0.22/0.61  thf(d10_xboole_0, axiom,
% 0.22/0.61    (![A:$i,B:$i]:
% 0.22/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.61  thf('5', plain,
% 0.22/0.61      (![X7 : $i, X9 : $i]:
% 0.22/0.61         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.61  thf('6', plain,
% 0.22/0.61      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 0.22/0.61        | ((k1_tarski @ sk_A) = (sk_C_1)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.61  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('8', plain,
% 0.22/0.61      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.22/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.61  thf('9', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.61  thf('10', plain,
% 0.22/0.61      (![X7 : $i, X9 : $i]:
% 0.22/0.61         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.61  thf('11', plain,
% 0.22/0.61      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.22/0.61        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.61  thf(d1_enumset1, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.61       ( ![E:$i]:
% 0.22/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.61  thf(zf_stmt_1, axiom,
% 0.22/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.61  thf('12', plain,
% 0.22/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.61         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.22/0.61          | ((X24) = (X25))
% 0.22/0.61          | ((X24) = (X26))
% 0.22/0.61          | ((X24) = (X27)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.61  thf(t7_xboole_0, axiom,
% 0.22/0.61    (![A:$i]:
% 0.22/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.61  thf('13', plain,
% 0.22/0.61      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.61  thf('14', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.61  thf(d3_tarski, axiom,
% 0.22/0.61    (![A:$i,B:$i]:
% 0.22/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.61  thf('15', plain,
% 0.22/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.61          | (r2_hidden @ X2 @ X4)
% 0.22/0.61          | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.61  thf('16', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.61  thf('17', plain,
% 0.22/0.61      ((((sk_B_1) = (k1_xboole_0))
% 0.22/0.61        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.61  thf('18', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('19', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.22/0.61  thf(t69_enumset1, axiom,
% 0.22/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.61  thf('20', plain,
% 0.22/0.61      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.22/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.61  thf(t70_enumset1, axiom,
% 0.22/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.61  thf('21', plain,
% 0.22/0.61      (![X36 : $i, X37 : $i]:
% 0.22/0.61         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.22/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.61  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.61  thf(zf_stmt_3, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.61       ( ![E:$i]:
% 0.22/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.61  thf('22', plain,
% 0.22/0.61      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X33 @ X32)
% 0.22/0.61          | ~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.22/0.61          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.61  thf('23', plain,
% 0.22/0.61      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.22/0.61         (~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.22/0.61          | ~ (r2_hidden @ X33 @ (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.22/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.61  thf('24', plain,
% 0.22/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.61      inference('sup-', [status(thm)], ['21', '23'])).
% 0.22/0.61  thf('25', plain,
% 0.22/0.61      (![X0 : $i, X1 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.61      inference('sup-', [status(thm)], ['20', '24'])).
% 0.22/0.61  thf('26', plain, (~ (zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_A @ sk_A @ sk_A)),
% 0.22/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.22/0.61  thf('27', plain,
% 0.22/0.61      ((((sk_B @ sk_B_1) = (sk_A))
% 0.22/0.61        | ((sk_B @ sk_B_1) = (sk_A))
% 0.22/0.61        | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['12', '26'])).
% 0.22/0.61  thf('28', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.22/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.61  thf('29', plain,
% 0.22/0.61      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.61  thf(l1_zfmisc_1, axiom,
% 0.22/0.61    (![A:$i,B:$i]:
% 0.22/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.61  thf('30', plain,
% 0.22/0.61      (![X63 : $i, X65 : $i]:
% 0.22/0.61         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 0.22/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.61  thf('31', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.61  thf('32', plain,
% 0.22/0.61      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.61      inference('sup+', [status(thm)], ['28', '31'])).
% 0.22/0.61  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('34', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.22/0.61      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.22/0.61  thf('35', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['11', '34'])).
% 0.22/0.61  thf('36', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['11', '34'])).
% 0.22/0.61  thf('37', plain, ((~ (r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (sk_C_1)))),
% 0.22/0.61      inference('demod', [status(thm)], ['6', '35', '36'])).
% 0.22/0.61  thf('38', plain, (((sk_B_1) != (sk_C_1))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('39', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.22/0.61      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.22/0.61  thf('40', plain,
% 0.22/0.61      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.61  thf('41', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('sup+', [status(thm)], ['0', '3'])).
% 0.22/0.61  thf('42', plain,
% 0.22/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X2 @ X3)
% 0.22/0.61          | (r2_hidden @ X2 @ X4)
% 0.22/0.61          | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.61  thf('43', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.61  thf('44', plain,
% 0.22/0.61      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.61        | (r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['40', '43'])).
% 0.22/0.61  thf('45', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('46', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.22/0.61  thf('47', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['11', '34'])).
% 0.22/0.61  thf('48', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 0.22/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.61  thf('49', plain,
% 0.22/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.61         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.22/0.61          | ((X24) = (X25))
% 0.22/0.61          | ((X24) = (X26))
% 0.22/0.61          | ((X24) = (X27)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.61  thf('50', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['11', '34'])).
% 0.22/0.61  thf('51', plain,
% 0.22/0.61      (![X0 : $i, X1 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.61      inference('sup-', [status(thm)], ['20', '24'])).
% 0.22/0.61  thf('52', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.22/0.61          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.22/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.61  thf('53', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         (((X0) = (sk_A))
% 0.22/0.61          | ((X0) = (sk_A))
% 0.22/0.61          | ((X0) = (sk_A))
% 0.22/0.61          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.61      inference('sup-', [status(thm)], ['49', '52'])).
% 0.22/0.61  thf('54', plain,
% 0.22/0.61      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.22/0.61      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.61  thf('55', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.22/0.61      inference('sup-', [status(thm)], ['48', '54'])).
% 0.22/0.61  thf('56', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.61  thf('57', plain,
% 0.22/0.61      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.22/0.61      inference('sup+', [status(thm)], ['55', '56'])).
% 0.22/0.61  thf('58', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['11', '34'])).
% 0.22/0.61  thf('59', plain,
% 0.22/0.61      (((r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.22/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.61  thf('60', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('61', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.22/0.61      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.22/0.61  thf('62', plain, ($false), inference('demod', [status(thm)], ['39', '61'])).
% 0.22/0.61  
% 0.22/0.61  % SZS output end Refutation
% 0.22/0.61  
% 0.45/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
