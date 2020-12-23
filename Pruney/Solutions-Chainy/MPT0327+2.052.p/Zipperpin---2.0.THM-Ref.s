%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uovXLlqrf9

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:57 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  156 (14828 expanded)
%              Number of leaves         :   22 (4448 expanded)
%              Depth                    :   35
%              Number of atoms          : 1166 (115598 expanded)
%              Number of equality atoms :  101 (10230 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','19'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('35',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','19'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('65',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','70'])).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','74'])).

thf('76',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','73'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('89',plain,(
    ! [X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('92',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('102',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('103',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('109',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('114',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['100','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['90','99'])).

thf('119',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('121',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('126',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['121','124','125'])).

thf('127',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','74'])).

thf('129',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('131',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['126','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uovXLlqrf9
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.01/3.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.01/3.21  % Solved by: fo/fo7.sh
% 3.01/3.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.01/3.21  % done 3271 iterations in 2.700s
% 3.01/3.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.01/3.21  % SZS output start Refutation
% 3.01/3.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.01/3.21  thf(sk_A_type, type, sk_A: $i).
% 3.01/3.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.01/3.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.01/3.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.01/3.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.01/3.21  thf(sk_B_type, type, sk_B: $i).
% 3.01/3.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.01/3.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.01/3.21  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.01/3.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.01/3.21  thf(t140_zfmisc_1, conjecture,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( r2_hidden @ A @ B ) =>
% 3.01/3.21       ( ( k2_xboole_0 @
% 3.01/3.21           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 3.01/3.21         ( B ) ) ))).
% 3.01/3.21  thf(zf_stmt_0, negated_conjecture,
% 3.01/3.21    (~( ![A:$i,B:$i]:
% 3.01/3.21        ( ( r2_hidden @ A @ B ) =>
% 3.01/3.21          ( ( k2_xboole_0 @
% 3.01/3.21              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 3.01/3.21            ( B ) ) ) )),
% 3.01/3.21    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 3.01/3.21  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 3.01/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.21  thf(l1_zfmisc_1, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 3.01/3.21  thf('1', plain,
% 3.01/3.21      (![X36 : $i, X38 : $i]:
% 3.01/3.21         ((r1_tarski @ (k1_tarski @ X36) @ X38) | ~ (r2_hidden @ X36 @ X38))),
% 3.01/3.21      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 3.01/3.21  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 3.01/3.21      inference('sup-', [status(thm)], ['0', '1'])).
% 3.01/3.21  thf(t12_xboole_1, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.01/3.21  thf('3', plain,
% 3.01/3.21      (![X16 : $i, X17 : $i]:
% 3.01/3.21         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 3.01/3.21      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.01/3.21  thf('4', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 3.01/3.21      inference('sup-', [status(thm)], ['2', '3'])).
% 3.01/3.21  thf(t98_xboole_1, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.01/3.21  thf('5', plain,
% 3.01/3.21      (![X24 : $i, X25 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ X24 @ X25)
% 3.01/3.21           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.01/3.21  thf(d3_tarski, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( r1_tarski @ A @ B ) <=>
% 3.01/3.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.01/3.21  thf('6', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf(d10_xboole_0, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.01/3.21  thf('7', plain,
% 3.01/3.21      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 3.01/3.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.01/3.21  thf('8', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 3.01/3.21      inference('simplify', [status(thm)], ['7'])).
% 3.01/3.21  thf(t28_xboole_1, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.01/3.21  thf('9', plain,
% 3.01/3.21      (![X19 : $i, X20 : $i]:
% 3.01/3.21         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 3.01/3.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.01/3.21  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['8', '9'])).
% 3.01/3.21  thf(t100_xboole_1, axiom,
% 3.01/3.21    (![A:$i,B:$i]:
% 3.01/3.21     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.01/3.21  thf('11', plain,
% 3.01/3.21      (![X14 : $i, X15 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ X14 @ X15)
% 3.01/3.21           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.01/3.21  thf('12', plain,
% 3.01/3.21      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['10', '11'])).
% 3.01/3.21  thf(d5_xboole_0, axiom,
% 3.01/3.21    (![A:$i,B:$i,C:$i]:
% 3.01/3.21     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.01/3.21       ( ![D:$i]:
% 3.01/3.21         ( ( r2_hidden @ D @ C ) <=>
% 3.01/3.21           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.01/3.21  thf('13', plain,
% 3.01/3.21      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X8 @ X7)
% 3.01/3.21          | (r2_hidden @ X8 @ X5)
% 3.01/3.21          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.01/3.21  thf('14', plain,
% 3.01/3.21      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.01/3.21         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('simplify', [status(thm)], ['13'])).
% 3.01/3.21  thf('15', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['12', '14'])).
% 3.01/3.21  thf('16', plain,
% 3.01/3.21      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['10', '11'])).
% 3.01/3.21  thf('17', plain,
% 3.01/3.21      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X8 @ X7)
% 3.01/3.21          | ~ (r2_hidden @ X8 @ X6)
% 3.01/3.21          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.01/3.21  thf('18', plain,
% 3.01/3.21      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X8 @ X6)
% 3.01/3.21          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('simplify', [status(thm)], ['17'])).
% 3.01/3.21  thf('19', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 3.01/3.21          | ~ (r2_hidden @ X1 @ X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['16', '18'])).
% 3.01/3.21  thf('20', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 3.01/3.21      inference('clc', [status(thm)], ['15', '19'])).
% 3.01/3.21  thf('21', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 3.01/3.21      inference('sup-', [status(thm)], ['6', '20'])).
% 3.01/3.21  thf('22', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('23', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 3.01/3.21      inference('sup-', [status(thm)], ['0', '1'])).
% 3.01/3.21  thf('24', plain,
% 3.01/3.21      (![X19 : $i, X20 : $i]:
% 3.01/3.21         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 3.01/3.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.01/3.21  thf('25', plain,
% 3.01/3.21      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 3.01/3.21      inference('sup-', [status(thm)], ['23', '24'])).
% 3.01/3.21  thf('26', plain,
% 3.01/3.21      (![X14 : $i, X15 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ X14 @ X15)
% 3.01/3.21           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.01/3.21  thf('27', plain,
% 3.01/3.21      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 3.01/3.21         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['25', '26'])).
% 3.01/3.21  thf('28', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 3.01/3.21      inference('clc', [status(thm)], ['15', '19'])).
% 3.01/3.21  thf('29', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 3.01/3.21      inference('sup-', [status(thm)], ['27', '28'])).
% 3.01/3.21  thf('30', plain,
% 3.01/3.21      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 3.01/3.21      inference('sup-', [status(thm)], ['22', '29'])).
% 3.01/3.21  thf('31', plain,
% 3.01/3.21      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 3.01/3.21      inference('sup-', [status(thm)], ['22', '29'])).
% 3.01/3.21  thf('32', plain,
% 3.01/3.21      (![X16 : $i, X17 : $i]:
% 3.01/3.21         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 3.01/3.21      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.01/3.21  thf('33', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0) = (X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['31', '32'])).
% 3.01/3.21  thf(t1_boole, axiom,
% 3.01/3.21    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.01/3.21  thf('34', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 3.01/3.21      inference('cnf', [status(esa)], [t1_boole])).
% 3.01/3.21  thf('35', plain,
% 3.01/3.21      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 3.01/3.21      inference('sup+', [status(thm)], ['33', '34'])).
% 3.01/3.21  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.01/3.21      inference('demod', [status(thm)], ['30', '35'])).
% 3.01/3.21  thf('37', plain,
% 3.01/3.21      (![X11 : $i, X13 : $i]:
% 3.01/3.21         (((X11) = (X13))
% 3.01/3.21          | ~ (r1_tarski @ X13 @ X11)
% 3.01/3.21          | ~ (r1_tarski @ X11 @ X13))),
% 3.01/3.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.01/3.21  thf('38', plain,
% 3.01/3.21      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.01/3.21      inference('sup-', [status(thm)], ['36', '37'])).
% 3.01/3.21  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['21', '38'])).
% 3.01/3.21  thf('40', plain,
% 3.01/3.21      (![X24 : $i, X25 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ X24 @ X25)
% 3.01/3.21           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.01/3.21  thf('41', plain,
% 3.01/3.21      (![X24 : $i, X25 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ X24 @ X25)
% 3.01/3.21           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.01/3.21  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.01/3.21      inference('demod', [status(thm)], ['30', '35'])).
% 3.01/3.21  thf('43', plain,
% 3.01/3.21      (![X19 : $i, X20 : $i]:
% 3.01/3.21         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 3.01/3.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.01/3.21  thf('44', plain,
% 3.01/3.21      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['42', '43'])).
% 3.01/3.21  thf('45', plain,
% 3.01/3.21      (![X14 : $i, X15 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ X14 @ X15)
% 3.01/3.21           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.01/3.21  thf('46', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.01/3.21           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['44', '45'])).
% 3.01/3.21  thf('47', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.01/3.21           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['44', '45'])).
% 3.01/3.21  thf('48', plain,
% 3.01/3.21      (![X24 : $i, X25 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ X24 @ X25)
% 3.01/3.21           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.01/3.21  thf('49', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 3.01/3.21           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['47', '48'])).
% 3.01/3.21  thf('50', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 3.01/3.21      inference('cnf', [status(esa)], [t1_boole])).
% 3.01/3.21  thf('51', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.01/3.21      inference('demod', [status(thm)], ['49', '50'])).
% 3.01/3.21  thf('52', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['46', '51'])).
% 3.01/3.21  thf('53', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('54', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.01/3.21           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['44', '45'])).
% 3.01/3.21  thf('55', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 3.01/3.21      inference('clc', [status(thm)], ['15', '19'])).
% 3.01/3.21  thf('56', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['54', '55'])).
% 3.01/3.21  thf('57', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1)),
% 3.01/3.21      inference('sup-', [status(thm)], ['53', '56'])).
% 3.01/3.21  thf('58', plain,
% 3.01/3.21      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.01/3.21      inference('sup-', [status(thm)], ['36', '37'])).
% 3.01/3.21  thf('59', plain,
% 3.01/3.21      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['57', '58'])).
% 3.01/3.21  thf('60', plain, (![X1 : $i]: ((X1) = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.01/3.21      inference('demod', [status(thm)], ['52', '59'])).
% 3.01/3.21  thf(t91_xboole_1, axiom,
% 3.01/3.21    (![A:$i,B:$i,C:$i]:
% 3.01/3.21     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.01/3.21       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.01/3.21  thf('61', plain,
% 3.01/3.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 3.01/3.21           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.01/3.21  thf('62', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ X0 @ X1)
% 3.01/3.21           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['60', '61'])).
% 3.01/3.21  thf('63', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.01/3.21           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['41', '62'])).
% 3.01/3.21  thf('64', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0) = (X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['31', '32'])).
% 3.01/3.21  thf('65', plain,
% 3.01/3.21      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 3.01/3.21      inference('sup+', [status(thm)], ['33', '34'])).
% 3.01/3.21  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.01/3.21      inference('demod', [status(thm)], ['64', '65'])).
% 3.01/3.21  thf('67', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.01/3.21           = (k5_xboole_0 @ X1 @ X0))),
% 3.01/3.21      inference('demod', [status(thm)], ['63', '66'])).
% 3.01/3.21  thf('68', plain,
% 3.01/3.21      (![X0 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['40', '67'])).
% 3.01/3.21  thf('69', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.01/3.21      inference('demod', [status(thm)], ['64', '65'])).
% 3.01/3.21  thf('70', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.01/3.21      inference('demod', [status(thm)], ['68', '69'])).
% 3.01/3.21  thf('71', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((X1) = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 3.01/3.21      inference('sup+', [status(thm)], ['39', '70'])).
% 3.01/3.21  thf('72', plain,
% 3.01/3.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 3.01/3.21           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.01/3.21  thf('73', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.01/3.21      inference('demod', [status(thm)], ['71', '72'])).
% 3.01/3.21  thf('74', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ X0 @ X1)
% 3.01/3.21           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['5', '73'])).
% 3.01/3.21  thf('75', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.01/3.21         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 3.01/3.21      inference('sup+', [status(thm)], ['4', '74'])).
% 3.01/3.21  thf('76', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('77', plain,
% 3.01/3.21      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.01/3.21         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('simplify', [status(thm)], ['13'])).
% 3.01/3.21  thf('78', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.01/3.21          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 3.01/3.21      inference('sup-', [status(thm)], ['76', '77'])).
% 3.01/3.21  thf('79', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('80', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 3.01/3.21          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['78', '79'])).
% 3.01/3.21  thf('81', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 3.01/3.21      inference('simplify', [status(thm)], ['80'])).
% 3.01/3.21  thf('82', plain,
% 3.01/3.21      (![X16 : $i, X17 : $i]:
% 3.01/3.21         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 3.01/3.21      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.01/3.21  thf('83', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['81', '82'])).
% 3.01/3.21  thf('84', plain,
% 3.01/3.21      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 3.01/3.21         = (sk_B))),
% 3.01/3.21      inference('sup+', [status(thm)], ['75', '83'])).
% 3.01/3.21  thf('85', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ X0 @ X1)
% 3.01/3.21           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['5', '73'])).
% 3.01/3.21  thf('86', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 3.01/3.21         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B))),
% 3.01/3.21      inference('sup+', [status(thm)], ['84', '85'])).
% 3.01/3.21  thf('87', plain,
% 3.01/3.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 3.01/3.21           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.01/3.21  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['21', '38'])).
% 3.01/3.21  thf('89', plain, (![X1 : $i]: ((X1) = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.01/3.21      inference('demod', [status(thm)], ['52', '59'])).
% 3.01/3.21  thf('90', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 3.01/3.21         = (k1_tarski @ sk_A))),
% 3.01/3.21      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 3.01/3.21  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['21', '38'])).
% 3.01/3.21  thf('92', plain,
% 3.01/3.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 3.01/3.21           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.01/3.21  thf('93', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k1_xboole_0)
% 3.01/3.21           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 3.01/3.21      inference('sup+', [status(thm)], ['91', '92'])).
% 3.01/3.21  thf('94', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.01/3.21      inference('demod', [status(thm)], ['71', '72'])).
% 3.01/3.21  thf('95', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 3.01/3.21           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['93', '94'])).
% 3.01/3.21  thf('96', plain, (![X1 : $i]: ((X1) = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.01/3.21      inference('demod', [status(thm)], ['52', '59'])).
% 3.01/3.21  thf('97', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.01/3.21      inference('demod', [status(thm)], ['95', '96'])).
% 3.01/3.21  thf('98', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.01/3.21      inference('demod', [status(thm)], ['71', '72'])).
% 3.01/3.21  thf('99', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['97', '98'])).
% 3.01/3.21  thf('100', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 3.01/3.21         = (k1_tarski @ sk_A))),
% 3.01/3.21      inference('demod', [status(thm)], ['90', '99'])).
% 3.01/3.21  thf('101', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('102', plain,
% 3.01/3.21      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X4 @ X5)
% 3.01/3.21          | (r2_hidden @ X4 @ X6)
% 3.01/3.21          | (r2_hidden @ X4 @ X7)
% 3.01/3.21          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.01/3.21  thf('103', plain,
% 3.01/3.21      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.01/3.21         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 3.01/3.21          | (r2_hidden @ X4 @ X6)
% 3.01/3.21          | ~ (r2_hidden @ X4 @ X5))),
% 3.01/3.21      inference('simplify', [status(thm)], ['102'])).
% 3.01/3.21  thf('104', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.21         ((r1_tarski @ X0 @ X1)
% 3.01/3.21          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 3.01/3.21          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 3.01/3.21      inference('sup-', [status(thm)], ['101', '103'])).
% 3.01/3.21  thf('105', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('106', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.01/3.21          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.01/3.21          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.01/3.21      inference('sup-', [status(thm)], ['104', '105'])).
% 3.01/3.21  thf('107', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.01/3.21          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 3.01/3.21      inference('simplify', [status(thm)], ['106'])).
% 3.01/3.21  thf('108', plain,
% 3.01/3.21      (![X1 : $i, X3 : $i]:
% 3.01/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.01/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.01/3.21  thf('109', plain,
% 3.01/3.21      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.01/3.21         (~ (r2_hidden @ X8 @ X6)
% 3.01/3.21          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 3.01/3.21      inference('simplify', [status(thm)], ['17'])).
% 3.01/3.21  thf('110', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.01/3.21          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['108', '109'])).
% 3.01/3.21  thf('111', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 3.01/3.21           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 3.01/3.21          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 3.01/3.21             (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 3.01/3.21      inference('sup-', [status(thm)], ['107', '110'])).
% 3.01/3.21  thf('112', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 3.01/3.21          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.01/3.21      inference('simplify', [status(thm)], ['111'])).
% 3.01/3.21  thf('113', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 3.01/3.21      inference('simplify', [status(thm)], ['80'])).
% 3.01/3.21  thf('114', plain,
% 3.01/3.21      (![X11 : $i, X13 : $i]:
% 3.01/3.21         (((X11) = (X13))
% 3.01/3.21          | ~ (r1_tarski @ X13 @ X11)
% 3.01/3.21          | ~ (r1_tarski @ X11 @ X13))),
% 3.01/3.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.01/3.21  thf('115', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.01/3.21          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.01/3.21      inference('sup-', [status(thm)], ['113', '114'])).
% 3.01/3.21  thf('116', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k4_xboole_0 @ X1 @ X0)
% 3.01/3.21           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.01/3.21      inference('sup-', [status(thm)], ['112', '115'])).
% 3.01/3.21  thf('117', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 3.01/3.21         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 3.01/3.21            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 3.01/3.21      inference('sup+', [status(thm)], ['100', '116'])).
% 3.01/3.21  thf('118', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 3.01/3.21         = (k1_tarski @ sk_A))),
% 3.01/3.21      inference('demod', [status(thm)], ['90', '99'])).
% 3.01/3.21  thf('119', plain,
% 3.01/3.21      (((k1_tarski @ sk_A)
% 3.01/3.21         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 3.01/3.21            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 3.01/3.21      inference('demod', [status(thm)], ['117', '118'])).
% 3.01/3.21  thf('120', plain,
% 3.01/3.21      (![X24 : $i, X25 : $i]:
% 3.01/3.21         ((k2_xboole_0 @ X24 @ X25)
% 3.01/3.21           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.01/3.21  thf('121', plain,
% 3.01/3.21      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 3.01/3.21         (k1_tarski @ sk_A))
% 3.01/3.21         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 3.01/3.21            (k1_tarski @ sk_A)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['119', '120'])).
% 3.01/3.21  thf('122', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['97', '98'])).
% 3.01/3.21  thf('123', plain,
% 3.01/3.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 3.01/3.21           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 3.01/3.21      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.01/3.21  thf('124', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 3.01/3.21           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 3.01/3.21      inference('sup+', [status(thm)], ['122', '123'])).
% 3.01/3.21  thf('125', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]:
% 3.01/3.21         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.01/3.21      inference('demod', [status(thm)], ['95', '96'])).
% 3.01/3.21  thf('126', plain,
% 3.01/3.21      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 3.01/3.21         (k1_tarski @ sk_A)) = (sk_B))),
% 3.01/3.21      inference('demod', [status(thm)], ['121', '124', '125'])).
% 3.01/3.21  thf('127', plain,
% 3.01/3.21      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 3.01/3.21         (k1_tarski @ sk_A)) != (sk_B))),
% 3.01/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.21  thf('128', plain,
% 3.01/3.21      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.01/3.21         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 3.01/3.21      inference('sup+', [status(thm)], ['4', '74'])).
% 3.01/3.21  thf('129', plain,
% 3.01/3.21      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 3.01/3.21         (k1_tarski @ sk_A)) != (sk_B))),
% 3.01/3.21      inference('demod', [status(thm)], ['127', '128'])).
% 3.01/3.21  thf('130', plain,
% 3.01/3.21      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.01/3.21      inference('sup+', [status(thm)], ['97', '98'])).
% 3.01/3.21  thf('131', plain,
% 3.01/3.21      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 3.01/3.21         (k1_tarski @ sk_A)) != (sk_B))),
% 3.01/3.21      inference('demod', [status(thm)], ['129', '130'])).
% 3.01/3.21  thf('132', plain, ($false),
% 3.01/3.21      inference('simplify_reflect-', [status(thm)], ['126', '131'])).
% 3.01/3.21  
% 3.01/3.21  % SZS output end Refutation
% 3.01/3.21  
% 3.01/3.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
