%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XTguW4NOx1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:41 EST 2020

% Result     : Theorem 37.06s
% Output     : Refutation 37.06s
% Verified   : 
% Statistics : Number of formulae       :  115 (1247 expanded)
%              Number of leaves         :   20 ( 368 expanded)
%              Depth                    :   29
%              Number of atoms          : 1086 (11915 expanded)
%              Number of equality atoms :   91 (1001 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X37 ) )
        = ( k1_tarski @ X36 ) )
      | ( X36 = X37 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != X40 )
      | ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( X0
        = ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( sk_C @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_C @ X0 @ ( k2_tarski @ X1 @ X1 ) ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X38: $i,X39: $i,X41: $i] :
      ( ( r2_hidden @ X38 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X41 ) ) )
      | ( X38 = X41 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( X0
        = ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('24',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
       != sk_A )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,(
    ! [X39: $i,X40: $i] :
      ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) )
      | ( X0
        = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_A
      = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k2_tarski @ sk_A @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['3','32'])).

thf('34',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_A
      = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 != X35 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X35 ) )
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('49',plain,(
    ! [X35: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X35 ) )
     != ( k1_tarski @ X35 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('51',plain,(
    ! [X35: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X35 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['47','51'])).

thf('53',plain,
    ( sk_A
    = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X45 @ X46 ) @ X45 )
      | ( r2_hidden @ ( sk_C_1 @ X45 @ X46 ) @ X47 )
      | ~ ( r2_hidden @ X47 @ X46 )
      | ( X45
        = ( k1_setfam_1 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 )
      | ( X2
        = ( k1_setfam_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
      = ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,
    ( sk_A
    = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','52'])).

thf('60',plain,
    ( sk_A
    = ( sk_C @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','52'])).

thf('61',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X35: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X35 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('65',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k1_tarski @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('69',plain,(
    ! [X39: $i,X40: $i] :
      ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('70',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('72',plain,
    ( ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k4_xboole_0 @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X39: $i,X40: $i] :
      ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('74',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X45 @ X46 ) @ X45 )
      | ( r2_hidden @ ( sk_D @ X45 @ X46 ) @ X46 )
      | ( X45
        = ( k1_setfam_1 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('77',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_A @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X35: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X35 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('81',plain,(
    r2_hidden @ ( sk_D @ sk_A @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('83',plain,
    ( sk_A
    = ( sk_D @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X45 @ X46 ) @ X45 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X45 @ X46 ) @ ( sk_D @ X45 @ X46 ) )
      | ( X45
        = ( k1_setfam_1 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['67','74'])).

thf('87',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['67','74'])).

thf('88',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_setfam_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X35: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X35 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('92',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(simplify,[status(thm)],['92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XTguW4NOx1
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 37.06/37.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 37.06/37.30  % Solved by: fo/fo7.sh
% 37.06/37.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.06/37.30  % done 10453 iterations in 36.843s
% 37.06/37.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 37.06/37.30  % SZS output start Refutation
% 37.06/37.30  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 37.06/37.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 37.06/37.30  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 37.06/37.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 37.06/37.30  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 37.06/37.30  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 37.06/37.30  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 37.06/37.30  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 37.06/37.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 37.06/37.30  thf(sk_A_type, type, sk_A: $i).
% 37.06/37.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 37.06/37.30  thf(d10_xboole_0, axiom,
% 37.06/37.30    (![A:$i,B:$i]:
% 37.06/37.30     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 37.06/37.30  thf('0', plain,
% 37.06/37.30      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 37.06/37.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 37.06/37.30  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 37.06/37.30      inference('simplify', [status(thm)], ['0'])).
% 37.06/37.30  thf(l32_xboole_1, axiom,
% 37.06/37.30    (![A:$i,B:$i]:
% 37.06/37.30     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 37.06/37.30  thf('2', plain,
% 37.06/37.30      (![X7 : $i, X9 : $i]:
% 37.06/37.30         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 37.06/37.30      inference('cnf', [status(esa)], [l32_xboole_1])).
% 37.06/37.30  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['1', '2'])).
% 37.06/37.30  thf(t69_enumset1, axiom,
% 37.06/37.30    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 37.06/37.30  thf('4', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 37.06/37.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.06/37.30  thf(d3_tarski, axiom,
% 37.06/37.30    (![A:$i,B:$i]:
% 37.06/37.30     ( ( r1_tarski @ A @ B ) <=>
% 37.06/37.30       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 37.06/37.30  thf('5', plain,
% 37.06/37.30      (![X1 : $i, X3 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 37.06/37.30      inference('cnf', [status(esa)], [d3_tarski])).
% 37.06/37.30  thf(t20_zfmisc_1, axiom,
% 37.06/37.30    (![A:$i,B:$i]:
% 37.06/37.30     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 37.06/37.30         ( k1_tarski @ A ) ) <=>
% 37.06/37.30       ( ( A ) != ( B ) ) ))).
% 37.06/37.30  thf('6', plain,
% 37.06/37.30      (![X36 : $i, X37 : $i]:
% 37.06/37.30         (((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X37))
% 37.06/37.30            = (k1_tarski @ X36))
% 37.06/37.30          | ((X36) = (X37)))),
% 37.06/37.30      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 37.06/37.30  thf(t64_zfmisc_1, axiom,
% 37.06/37.30    (![A:$i,B:$i,C:$i]:
% 37.06/37.30     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 37.06/37.30       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 37.06/37.30  thf('7', plain,
% 37.06/37.30      (![X38 : $i, X39 : $i, X40 : $i]:
% 37.06/37.30         (((X38) != (X40))
% 37.06/37.30          | ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40))))),
% 37.06/37.30      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 37.06/37.30  thf('8', plain,
% 37.06/37.30      (![X39 : $i, X40 : $i]:
% 37.06/37.30         ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40)))),
% 37.06/37.30      inference('simplify', [status(thm)], ['7'])).
% 37.06/37.30  thf('9', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['6', '8'])).
% 37.06/37.30  thf('10', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 37.06/37.30          | ((X0) = (sk_C @ X1 @ (k1_tarski @ X0))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['5', '9'])).
% 37.06/37.30  thf('11', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (((X0) = (sk_C @ X1 @ (k2_tarski @ X0 @ X0)))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 37.06/37.30      inference('sup+', [status(thm)], ['4', '10'])).
% 37.06/37.30  thf('12', plain,
% 37.06/37.30      (![X7 : $i, X9 : $i]:
% 37.06/37.30         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 37.06/37.30      inference('cnf', [status(esa)], [l32_xboole_1])).
% 37.06/37.30  thf('13', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (((X1) = (sk_C @ X0 @ (k2_tarski @ X1 @ X1)))
% 37.06/37.30          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['11', '12'])).
% 37.06/37.30  thf('14', plain,
% 37.06/37.30      (![X1 : $i, X3 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 37.06/37.30      inference('cnf', [status(esa)], [d3_tarski])).
% 37.06/37.30  thf('15', plain,
% 37.06/37.30      (![X38 : $i, X39 : $i, X41 : $i]:
% 37.06/37.30         ((r2_hidden @ X38 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X41)))
% 37.06/37.30          | ((X38) = (X41))
% 37.06/37.30          | ~ (r2_hidden @ X38 @ X39))),
% 37.06/37.30      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 37.06/37.30  thf('16', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.06/37.30         ((r1_tarski @ X0 @ X1)
% 37.06/37.30          | ((sk_C @ X1 @ X0) = (X2))
% 37.06/37.30          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 37.06/37.30             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['14', '15'])).
% 37.06/37.30  thf('17', plain,
% 37.06/37.30      (![X1 : $i, X3 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 37.06/37.30      inference('cnf', [status(esa)], [d3_tarski])).
% 37.06/37.30  thf('18', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (((sk_C @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1) = (X0))
% 37.06/37.30          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 37.06/37.30          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['16', '17'])).
% 37.06/37.30  thf('19', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 37.06/37.30          | ((sk_C @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1) = (X0)))),
% 37.06/37.30      inference('simplify', [status(thm)], ['18'])).
% 37.06/37.30  thf('20', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 37.06/37.30          | ((X0) = (sk_C @ X1 @ (k1_tarski @ X0))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['5', '9'])).
% 37.06/37.30  thf('21', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.06/37.30         ((r1_tarski @ X0 @ X1)
% 37.06/37.30          | ((sk_C @ X1 @ X0) = (X2))
% 37.06/37.30          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 37.06/37.30             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['14', '15'])).
% 37.06/37.30  thf('22', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.06/37.30         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X0) @ X2)
% 37.06/37.30          | ((sk_C @ X2 @ (k1_tarski @ X0)) = (X1))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X0) @ X2))),
% 37.06/37.30      inference('sup+', [status(thm)], ['20', '21'])).
% 37.06/37.30  thf('23', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.06/37.30         (((sk_C @ X2 @ (k1_tarski @ X0)) = (X1))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X0) @ X2)
% 37.06/37.30          | (r2_hidden @ X0 @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 37.06/37.30      inference('simplify', [status(thm)], ['22'])).
% 37.06/37.30  thf(t11_setfam_1, conjecture,
% 37.06/37.30    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 37.06/37.30  thf(zf_stmt_0, negated_conjecture,
% 37.06/37.30    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 37.06/37.30    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 37.06/37.30  thf('24', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 37.06/37.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.06/37.30  thf('25', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (((sk_C @ X1 @ (k1_tarski @ X0)) != (sk_A))
% 37.06/37.30          | (r2_hidden @ X0 @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X0) @ 
% 37.06/37.30              (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A)))))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 37.06/37.30      inference('sup-', [status(thm)], ['23', '24'])).
% 37.06/37.30  thf('26', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (((X0) != (sk_A))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X1) @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X1) @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 37.06/37.30          | (r2_hidden @ X1 @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X1) @ 
% 37.06/37.30              (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['19', '25'])).
% 37.06/37.30  thf('27', plain,
% 37.06/37.30      (![X1 : $i]:
% 37.06/37.30         ((r2_hidden @ X1 @ 
% 37.06/37.30           (k4_xboole_0 @ (k1_tarski @ X1) @ 
% 37.06/37.30            (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A)))))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X1) @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('simplify', [status(thm)], ['26'])).
% 37.06/37.30  thf('28', plain,
% 37.06/37.30      (![X0 : $i]:
% 37.06/37.30         ((r2_hidden @ X0 @ k1_xboole_0)
% 37.06/37.30          | ((X0)
% 37.06/37.30              = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30                 (k2_tarski @ X0 @ X0)))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X0) @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('sup+', [status(thm)], ['13', '27'])).
% 37.06/37.30  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['1', '2'])).
% 37.06/37.30  thf('30', plain,
% 37.06/37.30      (![X39 : $i, X40 : $i]:
% 37.06/37.30         ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40)))),
% 37.06/37.30      inference('simplify', [status(thm)], ['7'])).
% 37.06/37.30  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 37.06/37.30      inference('sup-', [status(thm)], ['29', '30'])).
% 37.06/37.30  thf('32', plain,
% 37.06/37.30      (![X0 : $i]:
% 37.06/37.30         ((r1_tarski @ (k1_tarski @ X0) @ 
% 37.06/37.30           (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))
% 37.06/37.30          | ((X0)
% 37.06/37.30              = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30                 (k2_tarski @ X0 @ X0))))),
% 37.06/37.30      inference('clc', [status(thm)], ['28', '31'])).
% 37.06/37.30  thf('33', plain,
% 37.06/37.30      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 37.06/37.30        | ((sk_A)
% 37.06/37.30            = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30               (k2_tarski @ sk_A @ sk_A))))),
% 37.06/37.30      inference('sup+', [status(thm)], ['3', '32'])).
% 37.06/37.30  thf('34', plain,
% 37.06/37.30      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 37.06/37.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.06/37.30  thf('35', plain,
% 37.06/37.30      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 37.06/37.30        | ((sk_A)
% 37.06/37.30            = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30               (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('demod', [status(thm)], ['33', '34'])).
% 37.06/37.30  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['1', '2'])).
% 37.06/37.30  thf('37', plain,
% 37.06/37.30      (![X1 : $i, X3 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 37.06/37.30      inference('cnf', [status(esa)], [d3_tarski])).
% 37.06/37.30  thf('38', plain,
% 37.06/37.30      (![X38 : $i, X39 : $i, X40 : $i]:
% 37.06/37.30         ((r2_hidden @ X38 @ X39)
% 37.06/37.30          | ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40))))),
% 37.06/37.30      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 37.06/37.30  thf('39', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.06/37.30         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 37.06/37.30          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 37.06/37.30             X1))),
% 37.06/37.30      inference('sup-', [status(thm)], ['37', '38'])).
% 37.06/37.30  thf('40', plain,
% 37.06/37.30      (![X1 : $i, X3 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 37.06/37.30      inference('cnf', [status(esa)], [d3_tarski])).
% 37.06/37.30  thf('41', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 37.06/37.30          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['39', '40'])).
% 37.06/37.30  thf('42', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 37.06/37.30      inference('simplify', [status(thm)], ['41'])).
% 37.06/37.30  thf('43', plain,
% 37.06/37.30      (![X4 : $i, X6 : $i]:
% 37.06/37.30         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 37.06/37.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 37.06/37.30  thf('44', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 37.06/37.30          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['42', '43'])).
% 37.06/37.30  thf('45', plain,
% 37.06/37.30      (![X0 : $i]:
% 37.06/37.30         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 37.06/37.30          | ((k1_tarski @ X0)
% 37.06/37.30              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['36', '44'])).
% 37.06/37.30  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['1', '2'])).
% 37.06/37.30  thf('47', plain,
% 37.06/37.30      (![X0 : $i]:
% 37.06/37.30         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 37.06/37.30          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 37.06/37.30      inference('demod', [status(thm)], ['45', '46'])).
% 37.06/37.30  thf('48', plain,
% 37.06/37.30      (![X35 : $i, X36 : $i]:
% 37.06/37.30         (((X36) != (X35))
% 37.06/37.30          | ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X35))
% 37.06/37.30              != (k1_tarski @ X36)))),
% 37.06/37.30      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 37.06/37.30  thf('49', plain,
% 37.06/37.30      (![X35 : $i]:
% 37.06/37.30         ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X35))
% 37.06/37.30           != (k1_tarski @ X35))),
% 37.06/37.30      inference('simplify', [status(thm)], ['48'])).
% 37.06/37.30  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['1', '2'])).
% 37.06/37.30  thf('51', plain, (![X35 : $i]: ((k1_xboole_0) != (k1_tarski @ X35))),
% 37.06/37.30      inference('demod', [status(thm)], ['49', '50'])).
% 37.06/37.30  thf('52', plain,
% 37.06/37.30      (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)),
% 37.06/37.30      inference('clc', [status(thm)], ['47', '51'])).
% 37.06/37.30  thf('53', plain,
% 37.06/37.30      (((sk_A)
% 37.06/37.30         = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30            (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('clc', [status(thm)], ['35', '52'])).
% 37.06/37.30  thf('54', plain,
% 37.06/37.30      (![X1 : $i, X3 : $i]:
% 37.06/37.30         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 37.06/37.30      inference('cnf', [status(esa)], [d3_tarski])).
% 37.06/37.30  thf(d1_setfam_1, axiom,
% 37.06/37.30    (![A:$i,B:$i]:
% 37.06/37.30     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 37.06/37.30         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 37.06/37.30       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 37.06/37.30         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 37.06/37.30           ( ![C:$i]:
% 37.06/37.30             ( ( r2_hidden @ C @ B ) <=>
% 37.06/37.30               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 37.06/37.30  thf('55', plain,
% 37.06/37.30      (![X45 : $i, X46 : $i, X47 : $i]:
% 37.06/37.30         ((r2_hidden @ (sk_C_1 @ X45 @ X46) @ X45)
% 37.06/37.30          | (r2_hidden @ (sk_C_1 @ X45 @ X46) @ X47)
% 37.06/37.30          | ~ (r2_hidden @ X47 @ X46)
% 37.06/37.30          | ((X45) = (k1_setfam_1 @ X46))
% 37.06/37.30          | ((X46) = (k1_xboole_0)))),
% 37.06/37.30      inference('cnf', [status(esa)], [d1_setfam_1])).
% 37.06/37.30  thf('56', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.06/37.30         ((r1_tarski @ X0 @ X1)
% 37.06/37.30          | ((X0) = (k1_xboole_0))
% 37.06/37.30          | ((X2) = (k1_setfam_1 @ X0))
% 37.06/37.30          | (r2_hidden @ (sk_C_1 @ X2 @ X0) @ (sk_C @ X1 @ X0))
% 37.06/37.30          | (r2_hidden @ (sk_C_1 @ X2 @ X0) @ X2))),
% 37.06/37.30      inference('sup-', [status(thm)], ['54', '55'])).
% 37.06/37.30  thf('57', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         ((r2_hidden @ (sk_C_1 @ (sk_C @ X1 @ X0) @ X0) @ (sk_C @ X1 @ X0))
% 37.06/37.30          | ((sk_C @ X1 @ X0) = (k1_setfam_1 @ X0))
% 37.06/37.30          | ((X0) = (k1_xboole_0))
% 37.06/37.30          | (r1_tarski @ X0 @ X1))),
% 37.06/37.30      inference('eq_fact', [status(thm)], ['56'])).
% 37.06/37.30  thf('58', plain,
% 37.06/37.30      (((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ 
% 37.06/37.30         (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30          (k1_tarski @ sk_A)))
% 37.06/37.30        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 37.06/37.30           (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))))
% 37.06/37.30        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 37.06/37.30        | ((sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30            (k1_tarski @ sk_A)) = (k1_setfam_1 @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('sup+', [status(thm)], ['53', '57'])).
% 37.06/37.30  thf('59', plain,
% 37.06/37.30      (((sk_A)
% 37.06/37.30         = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30            (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('clc', [status(thm)], ['35', '52'])).
% 37.06/37.30  thf('60', plain,
% 37.06/37.30      (((sk_A)
% 37.06/37.30         = (sk_C @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30            (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('clc', [status(thm)], ['35', '52'])).
% 37.06/37.30  thf('61', plain,
% 37.06/37.30      (((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)
% 37.06/37.30        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 37.06/37.30           (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))))
% 37.06/37.30        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 37.06/37.30        | ((sk_A) = (k1_setfam_1 @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('demod', [status(thm)], ['58', '59', '60'])).
% 37.06/37.30  thf('62', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 37.06/37.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.06/37.30  thf('63', plain,
% 37.06/37.30      (((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)
% 37.06/37.30        | (r1_tarski @ (k1_tarski @ sk_A) @ 
% 37.06/37.30           (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))))
% 37.06/37.30        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 37.06/37.30      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 37.06/37.30  thf('64', plain, (![X35 : $i]: ((k1_xboole_0) != (k1_tarski @ X35))),
% 37.06/37.30      inference('demod', [status(thm)], ['49', '50'])).
% 37.06/37.30  thf('65', plain,
% 37.06/37.30      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 37.06/37.30         (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))))
% 37.06/37.30        | (r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A))),
% 37.06/37.30      inference('clc', [status(thm)], ['63', '64'])).
% 37.06/37.30  thf(l1_zfmisc_1, axiom,
% 37.06/37.30    (![A:$i,B:$i]:
% 37.06/37.30     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 37.06/37.30  thf('66', plain,
% 37.06/37.30      (![X32 : $i, X33 : $i]:
% 37.06/37.30         ((r2_hidden @ X32 @ X33) | ~ (r1_tarski @ (k1_tarski @ X32) @ X33))),
% 37.06/37.30      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 37.06/37.30  thf('67', plain,
% 37.06/37.30      (((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)
% 37.06/37.30        | (r2_hidden @ sk_A @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A)))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['65', '66'])).
% 37.06/37.30  thf('68', plain,
% 37.06/37.30      (![X1 : $i]:
% 37.06/37.30         ((r2_hidden @ X1 @ 
% 37.06/37.30           (k4_xboole_0 @ (k1_tarski @ X1) @ 
% 37.06/37.30            (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A)))))
% 37.06/37.30          | (r1_tarski @ (k1_tarski @ X1) @ 
% 37.06/37.30             (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('simplify', [status(thm)], ['26'])).
% 37.06/37.30  thf('69', plain,
% 37.06/37.30      (![X39 : $i, X40 : $i]:
% 37.06/37.30         ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40)))),
% 37.06/37.30      inference('simplify', [status(thm)], ['7'])).
% 37.06/37.30  thf('70', plain,
% 37.06/37.30      ((r1_tarski @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30        (k4_xboole_0 @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30         (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['68', '69'])).
% 37.06/37.30  thf('71', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 37.06/37.30          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['42', '43'])).
% 37.06/37.30  thf('72', plain,
% 37.06/37.30      (((k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A)))
% 37.06/37.30         = (k4_xboole_0 @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))) @ 
% 37.06/37.30            (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['70', '71'])).
% 37.06/37.30  thf('73', plain,
% 37.06/37.30      (![X39 : $i, X40 : $i]:
% 37.06/37.30         ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40)))),
% 37.06/37.30      inference('simplify', [status(thm)], ['7'])).
% 37.06/37.30  thf('74', plain,
% 37.06/37.30      (~ (r2_hidden @ sk_A @ (k1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('sup-', [status(thm)], ['72', '73'])).
% 37.06/37.30  thf('75', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)),
% 37.06/37.30      inference('clc', [status(thm)], ['67', '74'])).
% 37.06/37.30  thf('76', plain,
% 37.06/37.30      (![X45 : $i, X46 : $i]:
% 37.06/37.30         (~ (r2_hidden @ (sk_C_1 @ X45 @ X46) @ X45)
% 37.06/37.30          | (r2_hidden @ (sk_D @ X45 @ X46) @ X46)
% 37.06/37.30          | ((X45) = (k1_setfam_1 @ X46))
% 37.06/37.30          | ((X46) = (k1_xboole_0)))),
% 37.06/37.30      inference('cnf', [status(esa)], [d1_setfam_1])).
% 37.06/37.30  thf('77', plain,
% 37.06/37.30      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 37.06/37.30        | ((sk_A) = (k1_setfam_1 @ (k1_tarski @ sk_A)))
% 37.06/37.30        | (r2_hidden @ (sk_D @ sk_A @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['75', '76'])).
% 37.06/37.30  thf('78', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 37.06/37.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.06/37.30  thf('79', plain,
% 37.06/37.30      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 37.06/37.30        | (r2_hidden @ (sk_D @ sk_A @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 37.06/37.30  thf('80', plain, (![X35 : $i]: ((k1_xboole_0) != (k1_tarski @ X35))),
% 37.06/37.30      inference('demod', [status(thm)], ['49', '50'])).
% 37.06/37.30  thf('81', plain,
% 37.06/37.30      ((r2_hidden @ (sk_D @ sk_A @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_A))),
% 37.06/37.30      inference('clc', [status(thm)], ['79', '80'])).
% 37.06/37.30  thf('82', plain,
% 37.06/37.30      (![X0 : $i, X1 : $i]:
% 37.06/37.30         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['6', '8'])).
% 37.06/37.30  thf('83', plain, (((sk_A) = (sk_D @ sk_A @ (k1_tarski @ sk_A)))),
% 37.06/37.30      inference('sup-', [status(thm)], ['81', '82'])).
% 37.06/37.30  thf('84', plain,
% 37.06/37.30      (![X45 : $i, X46 : $i]:
% 37.06/37.30         (~ (r2_hidden @ (sk_C_1 @ X45 @ X46) @ X45)
% 37.06/37.30          | ~ (r2_hidden @ (sk_C_1 @ X45 @ X46) @ (sk_D @ X45 @ X46))
% 37.06/37.30          | ((X45) = (k1_setfam_1 @ X46))
% 37.06/37.30          | ((X46) = (k1_xboole_0)))),
% 37.06/37.30      inference('cnf', [status(esa)], [d1_setfam_1])).
% 37.06/37.30  thf('85', plain,
% 37.06/37.30      ((~ (r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)
% 37.06/37.30        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 37.06/37.30        | ((sk_A) = (k1_setfam_1 @ (k1_tarski @ sk_A)))
% 37.06/37.30        | ~ (r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A))),
% 37.06/37.30      inference('sup-', [status(thm)], ['83', '84'])).
% 37.06/37.30  thf('86', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)),
% 37.06/37.30      inference('clc', [status(thm)], ['67', '74'])).
% 37.06/37.30  thf('87', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ (k1_tarski @ sk_A)) @ sk_A)),
% 37.06/37.30      inference('clc', [status(thm)], ['67', '74'])).
% 37.06/37.30  thf('88', plain,
% 37.06/37.30      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 37.06/37.30        | ((sk_A) = (k1_setfam_1 @ (k1_tarski @ sk_A))))),
% 37.06/37.30      inference('demod', [status(thm)], ['85', '86', '87'])).
% 37.06/37.30  thf('89', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 37.06/37.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.06/37.30  thf('90', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 37.06/37.30      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 37.06/37.30  thf('91', plain, (![X35 : $i]: ((k1_xboole_0) != (k1_tarski @ X35))),
% 37.06/37.30      inference('demod', [status(thm)], ['49', '50'])).
% 37.06/37.30  thf('92', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 37.06/37.30      inference('sup-', [status(thm)], ['90', '91'])).
% 37.06/37.30  thf('93', plain, ($false), inference('simplify', [status(thm)], ['92'])).
% 37.06/37.30  
% 37.06/37.30  % SZS output end Refutation
% 37.06/37.30  
% 37.13/37.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
