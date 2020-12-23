%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.70syO8kILW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:07 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  111 (1091 expanded)
%              Number of leaves         :   12 ( 281 expanded)
%              Depth                    :   30
%              Number of atoms          : 1091 (11736 expanded)
%              Number of equality atoms :  143 (1593 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X9: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X9 ) )
      | ( ( sk_C @ X13 @ X9 )
        = X9 )
      | ( r2_hidden @ ( sk_C @ X13 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ k1_xboole_0 )
      | ( ( sk_C @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = sk_B )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X9 ) )
      | ( ( sk_C @ X13 @ X9 )
        = X9 )
      | ( r2_hidden @ ( sk_C @ X13 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = sk_B )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(eq_fact,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( sk_C @ sk_A @ sk_B )
      = sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_C @ sk_A @ sk_B )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X9 ) )
      | ( ( sk_C @ X13 @ X9 )
       != X9 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( sk_C @ sk_A @ sk_B )
     != sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C @ sk_A @ sk_B )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B != sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','59'])).

thf('61',plain,(
    ! [X9: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X9 ) )
      | ( ( sk_C @ X13 @ X9 )
       != X9 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_A @ X0 )
       != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
       != X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_D @ sk_A @ sk_A @ sk_A ) ) )
    | ( ( sk_C @ sk_A @ ( sk_D @ sk_A @ sk_A @ sk_A ) )
     != ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_D @ sk_A @ sk_A @ sk_A ) ) )
    | ( ( sk_C @ sk_A @ ( sk_D @ sk_A @ sk_A @ sk_A ) )
     != ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','59'])).

thf('68',plain,
    ( sk_A
    = ( k1_tarski @ ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( sk_D @ sk_A @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
        = ( sk_D @ sk_A @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
      = ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_tarski @ ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('75',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_A )
      | ( X1
        = ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( ( sk_D @ sk_A @ X0 @ sk_A )
        = ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','77'])).

thf('79',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('80',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( sk_D @ sk_A @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_D @ sk_A @ X0 @ X0 )
        = ( sk_D @ sk_A @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_A @ X0 @ X0 )
      = ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_A
    = ( k1_tarski @ ( sk_D @ sk_A @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('90',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ ( sk_D @ sk_A @ X0 @ sk_A ) ) )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','93'])).

thf('95',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.70syO8kILW
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.03/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.27  % Solved by: fo/fo7.sh
% 1.03/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.27  % done 1167 iterations in 0.809s
% 1.03/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.27  % SZS output start Refutation
% 1.03/1.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.27  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.03/1.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.03/1.27  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.03/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.27  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.03/1.27  thf(t66_zfmisc_1, conjecture,
% 1.03/1.27    (![A:$i,B:$i]:
% 1.03/1.27     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 1.03/1.27          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 1.03/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.27    (~( ![A:$i,B:$i]:
% 1.03/1.27        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 1.03/1.27             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 1.03/1.27    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 1.03/1.27  thf('0', plain,
% 1.03/1.27      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf(d5_xboole_0, axiom,
% 1.03/1.27    (![A:$i,B:$i,C:$i]:
% 1.03/1.27     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.03/1.27       ( ![D:$i]:
% 1.03/1.27         ( ( r2_hidden @ D @ C ) <=>
% 1.03/1.27           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.03/1.27  thf('1', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('2', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('eq_fact', [status(thm)], ['1'])).
% 1.03/1.27  thf('3', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('4', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.03/1.27  thf('5', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['4'])).
% 1.03/1.27  thf('6', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('eq_fact', [status(thm)], ['1'])).
% 1.03/1.27  thf('7', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.03/1.27      inference('clc', [status(thm)], ['5', '6'])).
% 1.03/1.27  thf(d1_tarski, axiom,
% 1.03/1.27    (![A:$i,B:$i]:
% 1.03/1.27     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.03/1.27       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.03/1.27  thf('8', plain,
% 1.03/1.27      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X12 @ X11)
% 1.03/1.27          | ((X12) = (X9))
% 1.03/1.27          | ((X11) != (k1_tarski @ X9)))),
% 1.03/1.27      inference('cnf', [status(esa)], [d1_tarski])).
% 1.03/1.27  thf('9', plain,
% 1.03/1.27      (![X9 : $i, X12 : $i]:
% 1.03/1.27         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['8'])).
% 1.03/1.27  thf('10', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.03/1.27          | ((sk_D @ X1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['7', '9'])).
% 1.03/1.27  thf('11', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('eq_fact', [status(thm)], ['1'])).
% 1.03/1.27  thf('12', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf(t4_boole, axiom,
% 1.03/1.27    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.03/1.27  thf('13', plain,
% 1.03/1.27      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [t4_boole])).
% 1.03/1.27  thf('14', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X4 @ X3)
% 1.03/1.27          | ~ (r2_hidden @ X4 @ X2)
% 1.03/1.27          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('15', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X4 @ X2)
% 1.03/1.27          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['14'])).
% 1.03/1.27  thf('16', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.03/1.27      inference('sup-', [status(thm)], ['13', '15'])).
% 1.03/1.27  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.03/1.27      inference('condensation', [status(thm)], ['16'])).
% 1.03/1.27  thf('18', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.03/1.27          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['12', '17'])).
% 1.03/1.27  thf('19', plain,
% 1.03/1.27      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [t4_boole])).
% 1.03/1.27  thf('20', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.03/1.27          | ((X1) = (k1_xboole_0)))),
% 1.03/1.27      inference('demod', [status(thm)], ['18', '19'])).
% 1.03/1.27  thf('21', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('eq_fact', [status(thm)], ['1'])).
% 1.03/1.27  thf('22', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('23', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((X0) = (k4_xboole_0 @ X0 @ X0))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['21', '22'])).
% 1.03/1.27  thf('24', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.03/1.27      inference('condensation', [status(thm)], ['16'])).
% 1.03/1.27  thf('26', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.03/1.27          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['24', '25'])).
% 1.03/1.27  thf('27', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('28', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 1.03/1.27          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.03/1.27          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['26', '27'])).
% 1.03/1.27  thf('29', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.03/1.27          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['28'])).
% 1.03/1.27  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.03/1.27      inference('condensation', [status(thm)], ['16'])).
% 1.03/1.27  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.03/1.27      inference('clc', [status(thm)], ['29', '30'])).
% 1.03/1.27  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.03/1.27      inference('clc', [status(thm)], ['29', '30'])).
% 1.03/1.27  thf('33', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((X0) = (k1_xboole_0))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.03/1.27          | ((X0) = (k1_xboole_0)))),
% 1.03/1.27      inference('demod', [status(thm)], ['23', '31', '32'])).
% 1.03/1.27  thf('34', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['33'])).
% 1.03/1.27  thf('35', plain,
% 1.03/1.27      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('36', plain,
% 1.03/1.27      (![X9 : $i, X13 : $i]:
% 1.03/1.27         (((X13) = (k1_tarski @ X9))
% 1.03/1.27          | ((sk_C @ X13 @ X9) = (X9))
% 1.03/1.27          | (r2_hidden @ (sk_C @ X13 @ X9) @ X13))),
% 1.03/1.27      inference('cnf', [status(esa)], [d1_tarski])).
% 1.03/1.27  thf('37', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X0 @ X1)
% 1.03/1.27          | (r2_hidden @ X0 @ X2)
% 1.03/1.27          | (r2_hidden @ X0 @ X3)
% 1.03/1.27          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('38', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.27         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | (r2_hidden @ X0 @ X2)
% 1.03/1.27          | ~ (r2_hidden @ X0 @ X1))),
% 1.03/1.27      inference('simplify', [status(thm)], ['37'])).
% 1.03/1.27  thf('39', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.27         (((sk_C @ X0 @ X1) = (X1))
% 1.03/1.27          | ((X0) = (k1_tarski @ X1))
% 1.03/1.27          | (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 1.03/1.27          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['36', '38'])).
% 1.03/1.27  thf('40', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_C @ sk_A @ X0) @ k1_xboole_0)
% 1.03/1.27          | (r2_hidden @ (sk_C @ sk_A @ X0) @ (k1_tarski @ sk_B))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (X0)))),
% 1.03/1.27      inference('sup+', [status(thm)], ['35', '39'])).
% 1.03/1.27  thf('41', plain,
% 1.03/1.27      (![X9 : $i, X12 : $i]:
% 1.03/1.27         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['8'])).
% 1.03/1.27  thf('42', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_C @ sk_A @ X0) = (X0))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | (r2_hidden @ (sk_C @ sk_A @ X0) @ k1_xboole_0)
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (sk_B)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['40', '41'])).
% 1.03/1.27  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.03/1.27      inference('condensation', [status(thm)], ['16'])).
% 1.03/1.27  thf('44', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_C @ sk_A @ X0) = (sk_B))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['42', '43'])).
% 1.03/1.27  thf('45', plain,
% 1.03/1.27      (![X9 : $i, X13 : $i]:
% 1.03/1.27         (((X13) = (k1_tarski @ X9))
% 1.03/1.27          | ((sk_C @ X13 @ X9) = (X9))
% 1.03/1.27          | (r2_hidden @ (sk_C @ X13 @ X9) @ X13))),
% 1.03/1.27      inference('cnf', [status(esa)], [d1_tarski])).
% 1.03/1.27  thf('46', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         ((r2_hidden @ sk_B @ sk_A)
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (X0))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (X0))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0)))),
% 1.03/1.27      inference('sup+', [status(thm)], ['44', '45'])).
% 1.03/1.27  thf('47', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (X0))
% 1.03/1.27          | (r2_hidden @ sk_B @ sk_A))),
% 1.03/1.27      inference('simplify', [status(thm)], ['46'])).
% 1.03/1.27  thf('48', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_C @ sk_A @ X0) = (sk_B))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['42', '43'])).
% 1.03/1.27  thf('49', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((X0) != (sk_B))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) = (sk_B)))),
% 1.03/1.27      inference('eq_fact', [status(thm)], ['48'])).
% 1.03/1.27  thf('50', plain,
% 1.03/1.27      ((((sk_C @ sk_A @ sk_B) = (sk_B)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['49'])).
% 1.03/1.27  thf('51', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('52', plain, (((sk_C @ sk_A @ sk_B) = (sk_B))),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 1.03/1.27  thf('53', plain,
% 1.03/1.27      (![X9 : $i, X13 : $i]:
% 1.03/1.27         (((X13) = (k1_tarski @ X9))
% 1.03/1.27          | ((sk_C @ X13 @ X9) != (X9))
% 1.03/1.27          | ~ (r2_hidden @ (sk_C @ X13 @ X9) @ X13))),
% 1.03/1.27      inference('cnf', [status(esa)], [d1_tarski])).
% 1.03/1.27  thf('54', plain,
% 1.03/1.27      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.03/1.27        | ((sk_C @ sk_A @ sk_B) != (sk_B))
% 1.03/1.27        | ((sk_A) = (k1_tarski @ sk_B)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['52', '53'])).
% 1.03/1.27  thf('55', plain, (((sk_C @ sk_A @ sk_B) = (sk_B))),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 1.03/1.27  thf('56', plain,
% 1.03/1.27      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.03/1.27        | ((sk_B) != (sk_B))
% 1.03/1.27        | ((sk_A) = (k1_tarski @ sk_B)))),
% 1.03/1.27      inference('demod', [status(thm)], ['54', '55'])).
% 1.03/1.27  thf('57', plain,
% 1.03/1.27      ((((sk_A) = (k1_tarski @ sk_B)) | ~ (r2_hidden @ sk_B @ sk_A))),
% 1.03/1.27      inference('simplify', [status(thm)], ['56'])).
% 1.03/1.27  thf('58', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('59', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 1.03/1.27  thf('60', plain,
% 1.03/1.27      (![X0 : $i]: (((sk_C @ sk_A @ X0) = (X0)) | ((sk_A) = (k1_tarski @ X0)))),
% 1.03/1.27      inference('clc', [status(thm)], ['47', '59'])).
% 1.03/1.27  thf('61', plain,
% 1.03/1.27      (![X9 : $i, X13 : $i]:
% 1.03/1.27         (((X13) = (k1_tarski @ X9))
% 1.03/1.27          | ((sk_C @ X13 @ X9) != (X9))
% 1.03/1.27          | ~ (r2_hidden @ (sk_C @ X13 @ X9) @ X13))),
% 1.03/1.27      inference('cnf', [status(esa)], [d1_tarski])).
% 1.03/1.27  thf('62', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X0 @ sk_A)
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_C @ sk_A @ X0) != (X0))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['60', '61'])).
% 1.03/1.27  thf('63', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_C @ sk_A @ X0) != (X0))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.03/1.27      inference('simplify', [status(thm)], ['62'])).
% 1.03/1.27  thf('64', plain,
% 1.03/1.27      ((((sk_A) = (k1_xboole_0))
% 1.03/1.27        | ((sk_A) = (k1_tarski @ (sk_D @ sk_A @ sk_A @ sk_A)))
% 1.03/1.27        | ((sk_C @ sk_A @ (sk_D @ sk_A @ sk_A @ sk_A))
% 1.03/1.27            != (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['34', '63'])).
% 1.03/1.27  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('66', plain,
% 1.03/1.27      ((((sk_A) = (k1_tarski @ (sk_D @ sk_A @ sk_A @ sk_A)))
% 1.03/1.27        | ((sk_C @ sk_A @ (sk_D @ sk_A @ sk_A @ sk_A))
% 1.03/1.27            != (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 1.03/1.27  thf('67', plain,
% 1.03/1.27      (![X0 : $i]: (((sk_C @ sk_A @ X0) = (X0)) | ((sk_A) = (k1_tarski @ X0)))),
% 1.03/1.27      inference('clc', [status(thm)], ['47', '59'])).
% 1.03/1.27  thf('68', plain, (((sk_A) = (k1_tarski @ (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('clc', [status(thm)], ['66', '67'])).
% 1.03/1.27  thf('69', plain,
% 1.03/1.27      (![X9 : $i, X12 : $i]:
% 1.03/1.27         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['8'])).
% 1.03/1.27  thf('70', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X0 @ sk_A) | ((X0) = (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['68', '69'])).
% 1.03/1.27  thf('71', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_A) = (k1_xboole_0))
% 1.03/1.27          | ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['20', '70'])).
% 1.03/1.27  thf('72', plain, (((sk_A) != (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('73', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_D @ sk_A @ sk_A @ sk_A))),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 1.03/1.27  thf('74', plain, (((sk_A) = (k1_tarski @ (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('clc', [status(thm)], ['66', '67'])).
% 1.03/1.27  thf('75', plain,
% 1.03/1.27      (![X0 : $i]: ((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ k1_xboole_0)))),
% 1.03/1.27      inference('sup+', [status(thm)], ['73', '74'])).
% 1.03/1.27  thf('76', plain,
% 1.03/1.27      (![X9 : $i, X12 : $i]:
% 1.03/1.27         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['8'])).
% 1.03/1.27  thf('77', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X1 @ sk_A) | ((X1) = (sk_D @ sk_A @ X0 @ k1_xboole_0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['75', '76'])).
% 1.03/1.27  thf('78', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (((sk_A) = (k4_xboole_0 @ sk_A @ X0))
% 1.03/1.27          | ((sk_D @ sk_A @ X0 @ sk_A) = (sk_D @ sk_A @ X1 @ k1_xboole_0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['11', '77'])).
% 1.03/1.27  thf('79', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('80', plain,
% 1.03/1.27      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.27         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.27          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.03/1.27          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.27      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.27  thf('81', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.03/1.27          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.03/1.27          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['79', '80'])).
% 1.03/1.27  thf('82', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.03/1.27          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.03/1.27      inference('simplify', [status(thm)], ['81'])).
% 1.03/1.27  thf('83', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.03/1.27      inference('clc', [status(thm)], ['29', '30'])).
% 1.03/1.27  thf('84', plain,
% 1.03/1.27      (![X0 : $i, X1 : $i]:
% 1.03/1.27         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.03/1.27      inference('demod', [status(thm)], ['82', '83'])).
% 1.03/1.27  thf('85', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (~ (r2_hidden @ X0 @ sk_A) | ((X0) = (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['68', '69'])).
% 1.03/1.27  thf('86', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_A) = (k1_xboole_0))
% 1.03/1.27          | ((sk_D @ sk_A @ X0 @ X0) = (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('sup-', [status(thm)], ['84', '85'])).
% 1.03/1.27  thf('87', plain, (((sk_A) != (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('88', plain,
% 1.03/1.27      (![X0 : $i]: ((sk_D @ sk_A @ X0 @ X0) = (sk_D @ sk_A @ sk_A @ sk_A))),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 1.03/1.27  thf('89', plain, (((sk_A) = (k1_tarski @ (sk_D @ sk_A @ sk_A @ sk_A)))),
% 1.03/1.27      inference('clc', [status(thm)], ['66', '67'])).
% 1.03/1.27  thf('90', plain,
% 1.03/1.27      (![X0 : $i]: ((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ X0)))),
% 1.03/1.27      inference('sup+', [status(thm)], ['88', '89'])).
% 1.03/1.27  thf('91', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_A) = (k1_tarski @ (sk_D @ sk_A @ X0 @ sk_A)))
% 1.03/1.27          | ((sk_A) = (k4_xboole_0 @ sk_A @ X0)))),
% 1.03/1.27      inference('sup+', [status(thm)], ['78', '90'])).
% 1.03/1.27  thf('92', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_A) = (k1_tarski @ X0))
% 1.03/1.27          | ((sk_A) = (k4_xboole_0 @ sk_A @ (k1_tarski @ X0)))
% 1.03/1.27          | ((sk_A) = (k4_xboole_0 @ sk_A @ (k1_tarski @ X0))))),
% 1.03/1.27      inference('sup+', [status(thm)], ['10', '91'])).
% 1.03/1.27  thf('93', plain,
% 1.03/1.27      (![X0 : $i]:
% 1.03/1.27         (((sk_A) = (k4_xboole_0 @ sk_A @ (k1_tarski @ X0)))
% 1.03/1.27          | ((sk_A) = (k1_tarski @ X0)))),
% 1.03/1.27      inference('simplify', [status(thm)], ['92'])).
% 1.03/1.27  thf('94', plain,
% 1.03/1.27      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 1.03/1.27      inference('sup+', [status(thm)], ['0', '93'])).
% 1.03/1.27  thf('95', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 1.03/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.27  thf('97', plain, ($false),
% 1.03/1.27      inference('simplify_reflect-', [status(thm)], ['94', '95', '96'])).
% 1.03/1.27  
% 1.03/1.27  % SZS output end Refutation
% 1.03/1.27  
% 1.09/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
