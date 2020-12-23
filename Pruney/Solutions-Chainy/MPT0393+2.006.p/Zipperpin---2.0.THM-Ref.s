%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RBF7Otwizf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:41 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 432 expanded)
%              Number of leaves         :   28 ( 134 expanded)
%              Depth                    :   23
%              Number of atoms          : 1021 (3662 expanded)
%              Number of equality atoms :   94 ( 396 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X42 @ X41 ) @ X41 )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X36: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('5',plain,(
    ! [X37: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X37 ) @ ( k3_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( sk_C_2 @ X42 @ X41 ) )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('18',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('25',plain,(
    ! [X36: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('26',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('30',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['24','25'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('59',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['24','25'])).

thf('60',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('65',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','68'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
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

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t5_setfam_1,axiom,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf('73',plain,(
    ! [X40: $i] :
      ( ( ( k1_setfam_1 @ X40 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t5_setfam_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X2 )
      | ( ( k1_setfam_1 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X15 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('85',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['78','86'])).

thf('88',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('99',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','104'])).

thf('106',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RBF7Otwizf
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 647 iterations in 0.455s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.89  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.89  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.68/0.89  thf(t6_setfam_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.68/0.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      (![X41 : $i, X42 : $i]:
% 0.68/0.89         (((X41) = (k1_xboole_0))
% 0.68/0.89          | (r2_hidden @ (sk_C_2 @ X42 @ X41) @ X41)
% 0.68/0.89          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.68/0.89  thf(d1_tarski, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.68/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X28 @ X27)
% 0.68/0.89          | ((X28) = (X25))
% 0.68/0.89          | ((X27) != (k1_tarski @ X25)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d1_tarski])).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (![X25 : $i, X28 : $i]:
% 0.68/0.89         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['1'])).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.89          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['0', '2'])).
% 0.68/0.89  thf(t31_zfmisc_1, axiom,
% 0.68/0.89    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.68/0.89  thf('4', plain, (![X36 : $i]: ((k3_tarski @ (k1_tarski @ X36)) = (X36))),
% 0.68/0.89      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.68/0.89  thf(t3_setfam_1, axiom,
% 0.68/0.89    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      (![X37 : $i]: (r1_tarski @ (k1_setfam_1 @ X37) @ (k3_tarski @ X37))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.68/0.89      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf(d10_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (![X10 : $i, X12 : $i]:
% 0.68/0.89         (((X10) = (X12))
% 0.68/0.89          | ~ (r1_tarski @ X12 @ X10)
% 0.68/0.89          | ~ (r1_tarski @ X10 @ X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.89          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['3', '8'])).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X41 : $i, X42 : $i]:
% 0.68/0.89         (((X41) = (k1_xboole_0))
% 0.68/0.89          | ~ (r1_tarski @ X42 @ (sk_C_2 @ X42 @ X41))
% 0.68/0.89          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ X0)
% 0.68/0.89          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.89          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('13', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.68/0.89      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.89          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['11', '13'])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.89          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.89      inference('simplify', [status(thm)], ['14'])).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.89      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.89          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf(t11_setfam_1, conjecture,
% 0.68/0.89    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.68/0.89  thf('18', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.68/0.89  thf('20', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.68/0.89         (((X26) != (X25))
% 0.68/0.89          | (r2_hidden @ X26 @ X27)
% 0.68/0.89          | ((X27) != (k1_tarski @ X25)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d1_tarski])).
% 0.68/0.89  thf('22', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.68/0.89      inference('simplify', [status(thm)], ['21'])).
% 0.68/0.89  thf('23', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.68/0.89      inference('sup+', [status(thm)], ['20', '22'])).
% 0.68/0.89  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.89  thf('25', plain, (![X36 : $i]: ((k3_tarski @ (k1_tarski @ X36)) = (X36))),
% 0.68/0.89      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.68/0.89  thf('26', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('27', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.68/0.89      inference('demod', [status(thm)], ['23', '26'])).
% 0.68/0.89  thf(d3_tarski, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.89  thf('28', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('29', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.89  thf('30', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.68/0.89      inference('simplify', [status(thm)], ['21'])).
% 0.68/0.89  thf(d5_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.68/0.89       ( ![D:$i]:
% 0.68/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.89           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X4 @ X5)
% 0.68/0.89          | (r2_hidden @ X4 @ X6)
% 0.68/0.89          | (r2_hidden @ X4 @ X7)
% 0.68/0.89          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.89         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.68/0.89          | (r2_hidden @ X4 @ X6)
% 0.68/0.89          | ~ (r2_hidden @ X4 @ X5))),
% 0.68/0.89      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r2_hidden @ X0 @ X1)
% 0.68/0.89          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['30', '32'])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (![X25 : $i, X28 : $i]:
% 0.68/0.89         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['1'])).
% 0.68/0.89  thf('36', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.68/0.89          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.89  thf('37', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('38', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.89          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.68/0.89          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.68/0.89      inference('simplify', [status(thm)], ['38'])).
% 0.68/0.89  thf('40', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r2_hidden @ X1 @ X0)
% 0.68/0.89          | (r1_tarski @ (k1_tarski @ X1) @ 
% 0.68/0.89             (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['33', '39'])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('42', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X8 @ X7)
% 0.68/0.89          | (r2_hidden @ X8 @ X5)
% 0.68/0.89          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.89  thf('43', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.89         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.89          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['41', '43'])).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.68/0.89          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.68/0.89      inference('simplify', [status(thm)], ['46'])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      (![X10 : $i, X12 : $i]:
% 0.68/0.89         (((X10) = (X12))
% 0.68/0.89          | ~ (r1_tarski @ X12 @ X10)
% 0.68/0.89          | ~ (r1_tarski @ X10 @ X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.89          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['47', '48'])).
% 0.68/0.89  thf('50', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r2_hidden @ X1 @ X0)
% 0.68/0.89          | ((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['40', '49'])).
% 0.68/0.89  thf('51', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_tarski @ sk_A) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | (r2_hidden @ sk_A @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['29', '50'])).
% 0.68/0.89  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.89  thf('53', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | (r2_hidden @ sk_A @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.89  thf('54', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('55', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.89  thf('56', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.68/0.89      inference('simplify', [status(thm)], ['38'])).
% 0.68/0.89  thf('57', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | (r1_tarski @ (k1_tarski @ (k3_tarski @ k1_xboole_0)) @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['55', '56'])).
% 0.68/0.89  thf('58', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.89  thf('59', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('60', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['58', '59'])).
% 0.68/0.89  thf('61', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['57', '60'])).
% 0.68/0.89  thf('62', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.89          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['47', '48'])).
% 0.68/0.89  thf('63', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_xboole_0)
% 0.68/0.89            = (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))
% 0.68/0.89          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['61', '62'])).
% 0.68/0.89  thf('64', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X8 @ X7)
% 0.68/0.89          | ~ (r2_hidden @ X8 @ X6)
% 0.68/0.89          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.89  thf('65', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X8 @ X6)
% 0.68/0.89          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['64'])).
% 0.68/0.89  thf('66', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.68/0.89          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['63', '65'])).
% 0.68/0.89  thf('67', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.89         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.89  thf('68', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['66', '67'])).
% 0.68/0.89  thf('69', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1)
% 0.68/0.89          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['28', '68'])).
% 0.68/0.89  thf(t70_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.68/0.89  thf('70', plain,
% 0.68/0.89      (![X31 : $i, X32 : $i]:
% 0.68/0.89         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.68/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.89  thf(d1_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.89       ( ![E:$i]:
% 0.68/0.89         ( ( r2_hidden @ E @ D ) <=>
% 0.68/0.89           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.68/0.89  thf(zf_stmt_2, axiom,
% 0.68/0.89    (![E:$i,C:$i,B:$i,A:$i]:
% 0.68/0.89     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.68/0.89       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_3, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.89       ( ![E:$i]:
% 0.68/0.89         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.68/0.89  thf('71', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.89         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.68/0.89          | (r2_hidden @ X18 @ X22)
% 0.68/0.89          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.89  thf('72', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.89         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.68/0.89          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.68/0.89      inference('simplify', [status(thm)], ['71'])).
% 0.68/0.89  thf(t5_setfam_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.68/0.89       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.89  thf('73', plain,
% 0.68/0.89      (![X40 : $i]:
% 0.68/0.89         (((k1_setfam_1 @ X40) = (k1_xboole_0))
% 0.68/0.89          | ~ (r2_hidden @ k1_xboole_0 @ X40))),
% 0.68/0.89      inference('cnf', [status(esa)], [t5_setfam_1])).
% 0.68/0.89  thf('74', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.68/0.89          | ((k1_setfam_1 @ (k1_enumset1 @ X2 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['72', '73'])).
% 0.68/0.89  thf('75', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))
% 0.68/0.89          | (zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['70', '74'])).
% 0.68/0.89  thf('76', plain,
% 0.68/0.89      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         (((X14) != (X15)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.89  thf('77', plain,
% 0.68/0.89      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         ~ (zip_tseitin_0 @ X15 @ X15 @ X16 @ X13)),
% 0.68/0.89      inference('simplify', [status(thm)], ['76'])).
% 0.68/0.89  thf('78', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['75', '77'])).
% 0.68/0.89  thf('79', plain,
% 0.68/0.89      (![X31 : $i, X32 : $i]:
% 0.68/0.89         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.68/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.89  thf('80', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.89         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.68/0.89          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.68/0.89      inference('simplify', [status(thm)], ['71'])).
% 0.68/0.89  thf('81', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.68/0.89          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['79', '80'])).
% 0.68/0.89  thf('82', plain,
% 0.68/0.89      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.89  thf('83', plain,
% 0.68/0.89      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.68/0.89      inference('simplify', [status(thm)], ['82'])).
% 0.68/0.89  thf('84', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['81', '83'])).
% 0.68/0.89  thf(t4_setfam_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.68/0.89  thf('85', plain,
% 0.68/0.89      (![X38 : $i, X39 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_setfam_1 @ X38) @ X39) | ~ (r2_hidden @ X39 @ X38))),
% 0.68/0.89      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.68/0.89  thf('86', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.68/0.89      inference('sup-', [status(thm)], ['84', '85'])).
% 0.68/0.89  thf('87', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.68/0.89      inference('sup+', [status(thm)], ['78', '86'])).
% 0.68/0.89  thf('88', plain,
% 0.68/0.89      (![X10 : $i, X12 : $i]:
% 0.68/0.89         (((X10) = (X12))
% 0.68/0.89          | ~ (r1_tarski @ X12 @ X10)
% 0.68/0.89          | ~ (r1_tarski @ X10 @ X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('89', plain,
% 0.68/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['87', '88'])).
% 0.68/0.89  thf('90', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.68/0.89          | ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['69', '89'])).
% 0.68/0.89  thf('91', plain,
% 0.68/0.89      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['90'])).
% 0.68/0.89  thf('92', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.89          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['41', '43'])).
% 0.68/0.89  thf('93', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.89  thf('94', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X8 @ X6)
% 0.68/0.89          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['64'])).
% 0.68/0.89  thf('95', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.89          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['93', '94'])).
% 0.68/0.89  thf('96', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.68/0.89          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['92', '95'])).
% 0.68/0.89  thf('97', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.68/0.89      inference('simplify', [status(thm)], ['96'])).
% 0.68/0.89  thf('98', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.68/0.89      inference('simplify', [status(thm)], ['96'])).
% 0.68/0.89  thf('99', plain,
% 0.68/0.89      (![X10 : $i, X12 : $i]:
% 0.68/0.89         (((X10) = (X12))
% 0.68/0.89          | ~ (r1_tarski @ X12 @ X10)
% 0.68/0.89          | ~ (r1_tarski @ X10 @ X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('100', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.68/0.89          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['98', '99'])).
% 0.68/0.89  thf('101', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['97', '100'])).
% 0.68/0.89  thf('102', plain,
% 0.68/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X8 @ X6)
% 0.68/0.89          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['64'])).
% 0.68/0.89  thf('103', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.68/0.89          | ~ (r2_hidden @ X2 @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['101', '102'])).
% 0.68/0.89  thf('104', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.68/0.89      inference('condensation', [status(thm)], ['103'])).
% 0.68/0.89  thf('105', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.68/0.89      inference('sup-', [status(thm)], ['91', '104'])).
% 0.68/0.89  thf('106', plain, ($false), inference('sup-', [status(thm)], ['27', '105'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
