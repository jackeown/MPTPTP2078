%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X2BSVuAAA0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 121 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   27
%              Number of atoms          :  755 (1210 expanded)
%              Number of equality atoms :   84 ( 133 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_B )
      | ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_B )
      | ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_C )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_C )
      | ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) )
      | ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_B )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 )
        = sk_B )
      | ( r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ sk_C @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_A )
      | ( sk_C = sk_A )
      | ( sk_C = sk_A )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( sk_C = sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_A )
      | ( sk_B = sk_A )
      | ( sk_B = sk_A )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( sk_B = sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('51',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['10','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( sk_A = X0 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['1','55'])).

thf('57',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X2BSVuAAA0
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 138 iterations in 0.076s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(t25_zfmisc_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.56          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.56             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.56  thf('0', plain, (((sk_A) != (sk_C))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d1_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.56       ( ![E:$i]:
% 0.20/0.56         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, axiom,
% 0.20/0.56    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.56          | ((X9) = (X10))
% 0.20/0.56          | ((X9) = (X11))
% 0.20/0.56          | ((X9) = (X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('2', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(t70_enumset1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i]:
% 0.20/0.56         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.20/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_3, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.56       ( ![E:$i]:
% 0.20/0.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.56          | (r2_hidden @ X13 @ X17)
% 0.20/0.56          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.20/0.56          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.20/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.56          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['3', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.20/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.56  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['2', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.56          | ((X9) = (X10))
% 0.20/0.56          | ((X9) = (X11))
% 0.20/0.56          | ((X9) = (X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.56          | ((X9) = (X10))
% 0.20/0.56          | ((X9) = (X11))
% 0.20/0.56          | ((X9) = (X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.56          | ((X9) = (X10))
% 0.20/0.56          | ((X9) = (X11))
% 0.20/0.56          | ((X9) = (X12)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf(d4_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.56         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('eq_fact', [status(thm)], ['14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.56         = (k1_tarski @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | (r2_hidden @ X4 @ X2)
% 0.20/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) @ 
% 0.20/0.56             (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i]:
% 0.20/0.56         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.20/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.56          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.20/0.56          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.20/0.56         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.20/0.56          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ~ (zip_tseitin_0 @ 
% 0.20/0.56               (sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) @ sk_C @ 
% 0.20/0.56               sk_B @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['22', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_B))
% 0.20/0.56          | ((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_B))
% 0.20/0.56          | ((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_C))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_C))
% 0.20/0.56          | ((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('eq_fact', [status(thm)], ['14'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_C @ (k1_tarski @ sk_A))
% 0.20/0.56          | ((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_B))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ((sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) = (sk_B))
% 0.20/0.56          | (r2_hidden @ sk_C @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.56          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('eq_fact', [status(thm)], ['14'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.56          | (r2_hidden @ sk_C @ (k1_tarski @ sk_A))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | (r2_hidden @ sk_C @ (k1_tarski @ sk_A))
% 0.20/0.56          | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ~ (zip_tseitin_0 @ sk_C @ sk_A @ sk_A @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_C) = (sk_A))
% 0.20/0.56          | ((sk_C) = (sk_A))
% 0.20/0.56          | ((sk_C) = (sk_A))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['12', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ((sk_C) = (sk_A)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.56  thf('42', plain, (((sk_A) != (sk_C))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_B) = (sk_A))
% 0.20/0.56          | ((sk_B) = (sk_A))
% 0.20/0.56          | ((sk_B) = (sk_A))
% 0.20/0.56          | ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.56          | ((sk_B) = (sk_A)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.56  thf('48', plain, (((sk_A) != (sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | (r2_hidden @ X4 @ X1)
% 0.20/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '51'])).
% 0.20/0.56  thf('53', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '52'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('55', plain, (![X0 : $i]: ~ (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (![X0 : $i]: (((sk_A) = (X0)) | ((sk_A) = (X0)) | ((sk_A) = (X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '55'])).
% 0.20/0.56  thf('57', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.56  thf('58', plain, (((sk_A) != (sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '57'])).
% 0.20/0.56  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
