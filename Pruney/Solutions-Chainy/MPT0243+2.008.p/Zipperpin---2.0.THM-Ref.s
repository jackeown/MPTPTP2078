%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NXnEGdcTu7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:09 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 324 expanded)
%              Number of leaves         :   20 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  673 (2956 expanded)
%              Number of equality atoms :   34 (  74 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k1_tarski @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
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

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('29',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','12','23','28'])).

thf('30',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27 = X26 )
      | ( X27 = X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k2_tarski @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ ( k2_tarski @ X0 @ sk_B ) )
        = X0 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','12','23','41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X0 @ X2 ) )
        = X2 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X0 @ X2 ) )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,
    ( ( sk_A = sk_B )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('52',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference(eq_fact,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['25','52','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NXnEGdcTu7
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 427 iterations in 0.224s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.47/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.68  thf(t38_zfmisc_1, conjecture,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.47/0.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.68        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.47/0.68          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 0.47/0.68        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.47/0.68        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.47/0.68         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.47/0.68       ~ ((r2_hidden @ sk_B @ sk_C_1)) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf(t12_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X24 : $i, X25 : $i]:
% 0.47/0.68         (r1_tarski @ (k1_tarski @ X24) @ (k2_tarski @ X24 @ X25))),
% 0.47/0.68      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.47/0.68  thf(l1_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X21 : $i, X22 : $i]:
% 0.47/0.68         ((r2_hidden @ X21 @ X22) | ~ (r1_tarski @ (k1_tarski @ X21) @ X22))),
% 0.47/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (((r2_hidden @ sk_A @ sk_C_1)
% 0.47/0.68        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.47/0.68         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.47/0.68      inference('split', [status(esa)], ['6'])).
% 0.47/0.68  thf(d3_tarski, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.68          | (r2_hidden @ X0 @ X2)
% 0.47/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      ((![X0 : $i]:
% 0.47/0.68          ((r2_hidden @ X0 @ sk_C_1)
% 0.47/0.68           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.47/0.68         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (((r2_hidden @ sk_A @ sk_C_1))
% 0.47/0.68         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['5', '9'])).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.47/0.68       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.68  thf(t70_enumset1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X16 : $i, X17 : $i]:
% 0.47/0.68         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.47/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.68  thf(d1_enumset1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.47/0.68       ( ![E:$i]:
% 0.47/0.68         ( ( r2_hidden @ E @ D ) <=>
% 0.47/0.68           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.47/0.68  thf(zf_stmt_2, axiom,
% 0.47/0.68    (![E:$i,C:$i,B:$i,A:$i]:
% 0.47/0.68     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.47/0.68       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_3, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.47/0.68       ( ![E:$i]:
% 0.47/0.68         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.47/0.68          | (r2_hidden @ X9 @ X13)
% 0.47/0.68          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.68         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.47/0.68          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.47/0.68      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.47/0.68          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.47/0.68      inference('sup+', [status(thm)], ['13', '15'])).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.68         (((X5) != (X6)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X6 @ X6 @ X7 @ X4)),
% 0.47/0.68      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '18'])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      ((![X0 : $i]:
% 0.47/0.68          ((r2_hidden @ X0 @ sk_C_1)
% 0.47/0.68           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.47/0.68         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      (((r2_hidden @ sk_B @ sk_C_1))
% 0.47/0.68         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.47/0.68       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.68  thf('24', plain, (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['2', '12', '23'])).
% 0.47/0.68  thf('25', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.47/0.68  thf('26', plain,
% 0.47/0.68      (((r2_hidden @ sk_B @ sk_C_1)
% 0.47/0.68        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.47/0.68      inference('split', [status(esa)], ['26'])).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.47/0.68       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('split', [status(esa)], ['26'])).
% 0.47/0.68  thf('29', plain, (((r2_hidden @ sk_B @ sk_C_1))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '28'])).
% 0.47/0.68  thf('30', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.47/0.68  thf('31', plain,
% 0.47/0.68      (![X1 : $i, X3 : $i]:
% 0.47/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf('32', plain,
% 0.47/0.68      (![X21 : $i, X23 : $i]:
% 0.47/0.68         ((r1_tarski @ (k1_tarski @ X21) @ X23) | ~ (r2_hidden @ X21 @ X23))),
% 0.47/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.68  thf('33', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r1_tarski @ X0 @ X1)
% 0.47/0.68          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.68  thf(t25_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.47/0.68          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         (((X27) = (X26))
% 0.47/0.68          | ((X27) = (X28))
% 0.47/0.68          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k2_tarski @ X26 @ X28)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.47/0.68  thf('35', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X0))
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf('36', plain,
% 0.47/0.68      (![X1 : $i, X3 : $i]:
% 0.47/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf('37', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.68          | ((sk_C @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ X1)
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X2 @ X0) @ X1)
% 0.47/0.68          | ((sk_C @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 0.47/0.68          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((sk_C @ sk_C_1 @ (k2_tarski @ X0 @ sk_B)) = (X0))
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['30', '38'])).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.47/0.68      inference('split', [status(esa)], ['6'])).
% 0.47/0.68  thf('41', plain,
% 0.47/0.68      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.47/0.68       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('split', [status(esa)], ['6'])).
% 0.47/0.68  thf('42', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '41'])).
% 0.47/0.68  thf('43', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X0))
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      (![X1 : $i, X3 : $i]:
% 0.47/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.68          | ((sk_C @ X1 @ (k2_tarski @ X0 @ X2)) = (X2))
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X0 @ X2) @ X1)
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X0 @ X2) @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X0 @ X2) @ X1)
% 0.47/0.68          | ((sk_C @ X1 @ (k2_tarski @ X0 @ X2)) = (X2))
% 0.47/0.68          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((sk_C @ sk_C_1 @ (k2_tarski @ sk_A @ X0)) = (X0))
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ sk_A @ X0) @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['43', '47'])).
% 0.47/0.68  thf('49', plain,
% 0.47/0.68      ((((sk_A) = (sk_B))
% 0.47/0.68        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.47/0.68        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.68      inference('sup+', [status(thm)], ['39', '48'])).
% 0.47/0.68  thf('50', plain,
% 0.47/0.68      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) | ((sk_A) = (sk_B)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.68  thf('51', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.47/0.68  thf('52', plain, (((sk_A) = (sk_B))),
% 0.47/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.68  thf('53', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.47/0.68  thf('54', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X0))
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf('55', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (((X0) != (X1))
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.47/0.68      inference('eq_fact', [status(thm)], ['54'])).
% 0.47/0.68  thf('56', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X1 @ X1) @ X2)
% 0.47/0.68          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.68  thf('57', plain,
% 0.47/0.68      (![X1 : $i, X3 : $i]:
% 0.47/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf('58', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1)
% 0.47/0.68          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.68  thf('59', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r1_tarski @ (k2_tarski @ X0 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.68      inference('simplify', [status(thm)], ['58'])).
% 0.47/0.68  thf('60', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_C_1)),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '59'])).
% 0.47/0.68  thf('61', plain, ($false),
% 0.47/0.68      inference('demod', [status(thm)], ['25', '52', '60'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
