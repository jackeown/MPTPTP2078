%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7y0ORGafi

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:56 EST 2020

% Result     : Theorem 6.84s
% Output     : Refutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  160 (1813 expanded)
%              Number of leaves         :   27 ( 558 expanded)
%              Depth                    :   27
%              Number of atoms          : 1177 (13969 expanded)
%              Number of equality atoms :   92 (1172 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X60: $i,X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X63 )
      | ~ ( r2_hidden @ X62 @ X63 )
      | ~ ( r2_hidden @ X60 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ X14 @ X11 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
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
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','61'])).

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','64'])).

thf('66',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('72',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('74',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('79',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('82',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('87',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['76','91'])).

thf('93',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( r2_hidden @ X62 @ X61 )
      | ~ ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('100',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( r2_hidden @ X60 @ X61 )
      | ~ ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X60: $i,X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X63 )
      | ~ ( r2_hidden @ X62 @ X63 )
      | ~ ( r2_hidden @ X60 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('109',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('125',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['94','112','123','124'])).

thf('126',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('128',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('130',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['125','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7y0ORGafi
% 0.13/0.36  % Computer   : n009.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:52:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 6.84/7.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.84/7.07  % Solved by: fo/fo7.sh
% 6.84/7.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.84/7.07  % done 7031 iterations in 6.595s
% 6.84/7.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.84/7.07  % SZS output start Refutation
% 6.84/7.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.84/7.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.84/7.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.84/7.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.84/7.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.84/7.07  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 6.84/7.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.84/7.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.84/7.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.84/7.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.84/7.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.84/7.07  thf(sk_A_type, type, sk_A: $i).
% 6.84/7.07  thf(sk_B_type, type, sk_B: $i).
% 6.84/7.07  thf(d3_tarski, axiom,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( r1_tarski @ A @ B ) <=>
% 6.84/7.07       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.84/7.07  thf('0', plain,
% 6.84/7.07      (![X1 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.84/7.07      inference('cnf', [status(esa)], [d3_tarski])).
% 6.84/7.07  thf('1', plain,
% 6.84/7.07      (![X1 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.84/7.07      inference('cnf', [status(esa)], [d3_tarski])).
% 6.84/7.07  thf(t140_zfmisc_1, conjecture,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( r2_hidden @ A @ B ) =>
% 6.84/7.07       ( ( k2_xboole_0 @
% 6.84/7.07           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 6.84/7.07         ( B ) ) ))).
% 6.84/7.07  thf(zf_stmt_0, negated_conjecture,
% 6.84/7.07    (~( ![A:$i,B:$i]:
% 6.84/7.07        ( ( r2_hidden @ A @ B ) =>
% 6.84/7.07          ( ( k2_xboole_0 @
% 6.84/7.07              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 6.84/7.07            ( B ) ) ) )),
% 6.84/7.07    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 6.84/7.07  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 6.84/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.84/7.07  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 6.84/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.84/7.07  thf(t38_zfmisc_1, axiom,
% 6.84/7.07    (![A:$i,B:$i,C:$i]:
% 6.84/7.07     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 6.84/7.07       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 6.84/7.07  thf('4', plain,
% 6.84/7.07      (![X60 : $i, X62 : $i, X63 : $i]:
% 6.84/7.07         ((r1_tarski @ (k2_tarski @ X60 @ X62) @ X63)
% 6.84/7.07          | ~ (r2_hidden @ X62 @ X63)
% 6.84/7.07          | ~ (r2_hidden @ X60 @ X63))),
% 6.84/7.07      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.84/7.07  thf('5', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X0 @ sk_B)
% 6.84/7.07          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 6.84/7.07      inference('sup-', [status(thm)], ['3', '4'])).
% 6.84/7.07  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 6.84/7.07      inference('sup-', [status(thm)], ['2', '5'])).
% 6.84/7.07  thf(t69_enumset1, axiom,
% 6.84/7.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.84/7.07  thf('7', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 6.84/7.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.84/7.07  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 6.84/7.07      inference('demod', [status(thm)], ['6', '7'])).
% 6.84/7.07  thf(t12_xboole_1, axiom,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.84/7.07  thf('9', plain,
% 6.84/7.07      (![X22 : $i, X23 : $i]:
% 6.84/7.07         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 6.84/7.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.84/7.07  thf('10', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 6.84/7.07      inference('sup-', [status(thm)], ['8', '9'])).
% 6.84/7.07  thf(t98_xboole_1, axiom,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.84/7.07  thf('11', plain,
% 6.84/7.07      (![X28 : $i, X29 : $i]:
% 6.84/7.07         ((k2_xboole_0 @ X28 @ X29)
% 6.84/7.07           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.84/7.07  thf(t91_xboole_1, axiom,
% 6.84/7.07    (![A:$i,B:$i,C:$i]:
% 6.84/7.07     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.84/7.07       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 6.84/7.07  thf('12', plain,
% 6.84/7.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 6.84/7.07           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.84/7.07  thf(idempotence_k3_xboole_0, axiom,
% 6.84/7.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 6.84/7.07  thf('13', plain, (![X16 : $i]: ((k3_xboole_0 @ X16 @ X16) = (X16))),
% 6.84/7.07      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 6.84/7.07  thf(t100_xboole_1, axiom,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.84/7.07  thf('14', plain,
% 6.84/7.07      (![X20 : $i, X21 : $i]:
% 6.84/7.07         ((k4_xboole_0 @ X20 @ X21)
% 6.84/7.07           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.84/7.07  thf('15', plain,
% 6.84/7.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['13', '14'])).
% 6.84/7.07  thf(d5_xboole_0, axiom,
% 6.84/7.07    (![A:$i,B:$i,C:$i]:
% 6.84/7.07     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 6.84/7.07       ( ![D:$i]:
% 6.84/7.07         ( ( r2_hidden @ D @ C ) <=>
% 6.84/7.07           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 6.84/7.07  thf('16', plain,
% 6.84/7.07      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X14 @ X13)
% 6.84/7.07          | (r2_hidden @ X14 @ X11)
% 6.84/7.07          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 6.84/7.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.84/7.07  thf('17', plain,
% 6.84/7.07      (![X11 : $i, X12 : $i, X14 : $i]:
% 6.84/7.07         ((r2_hidden @ X14 @ X11)
% 6.84/7.07          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 6.84/7.07      inference('simplify', [status(thm)], ['16'])).
% 6.84/7.07  thf('18', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['15', '17'])).
% 6.84/7.07  thf('19', plain,
% 6.84/7.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['13', '14'])).
% 6.84/7.07  thf('20', plain,
% 6.84/7.07      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X14 @ X13)
% 6.84/7.07          | ~ (r2_hidden @ X14 @ X12)
% 6.84/7.07          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 6.84/7.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.84/7.07  thf('21', plain,
% 6.84/7.07      (![X11 : $i, X12 : $i, X14 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X14 @ X12)
% 6.84/7.07          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 6.84/7.07      inference('simplify', [status(thm)], ['20'])).
% 6.84/7.07  thf('22', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 6.84/7.07          | ~ (r2_hidden @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['19', '21'])).
% 6.84/7.07  thf('23', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 6.84/7.07      inference('clc', [status(thm)], ['18', '22'])).
% 6.84/7.07  thf('24', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ~ (r2_hidden @ X2 @ 
% 6.84/7.07            (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 6.84/7.07      inference('sup-', [status(thm)], ['12', '23'])).
% 6.84/7.07  thf('25', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ~ (r2_hidden @ X2 @ 
% 6.84/7.07            (k5_xboole_0 @ X1 @ 
% 6.84/7.07             (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))))),
% 6.84/7.07      inference('sup-', [status(thm)], ['11', '24'])).
% 6.84/7.07  thf('26', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         ~ (r2_hidden @ X0 @ 
% 6.84/7.07            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 6.84/7.07             (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['10', '25'])).
% 6.84/7.07  thf('27', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         (r1_tarski @ 
% 6.84/7.07          (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 6.84/7.07           (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)) @ 
% 6.84/7.07          X0)),
% 6.84/7.07      inference('sup-', [status(thm)], ['1', '26'])).
% 6.84/7.07  thf('28', plain,
% 6.84/7.07      (![X1 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.84/7.07      inference('cnf', [status(esa)], [d3_tarski])).
% 6.84/7.07  thf('29', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 6.84/7.07      inference('clc', [status(thm)], ['18', '22'])).
% 6.84/7.07  thf('30', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 6.84/7.07      inference('sup-', [status(thm)], ['28', '29'])).
% 6.84/7.07  thf('31', plain,
% 6.84/7.07      (![X1 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.84/7.07      inference('cnf', [status(esa)], [d3_tarski])).
% 6.84/7.07  thf(t5_boole, axiom,
% 6.84/7.07    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.84/7.07  thf('32', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 6.84/7.07      inference('cnf', [status(esa)], [t5_boole])).
% 6.84/7.07  thf('33', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 6.84/7.07          | ~ (r2_hidden @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['19', '21'])).
% 6.84/7.07  thf('34', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['32', '33'])).
% 6.84/7.07  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.84/7.07      inference('simplify', [status(thm)], ['34'])).
% 6.84/7.07  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.84/7.07      inference('sup-', [status(thm)], ['31', '35'])).
% 6.84/7.07  thf(d10_xboole_0, axiom,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.84/7.07  thf('37', plain,
% 6.84/7.07      (![X17 : $i, X19 : $i]:
% 6.84/7.07         (((X17) = (X19))
% 6.84/7.07          | ~ (r1_tarski @ X19 @ X17)
% 6.84/7.07          | ~ (r1_tarski @ X17 @ X19))),
% 6.84/7.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.84/7.07  thf('38', plain,
% 6.84/7.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['36', '37'])).
% 6.84/7.07  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['30', '38'])).
% 6.84/7.07  thf('40', plain,
% 6.84/7.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['36', '37'])).
% 6.84/7.07  thf('41', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['39', '40'])).
% 6.84/7.07  thf('42', plain,
% 6.84/7.07      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 6.84/7.07         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))
% 6.84/7.07         = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['27', '41'])).
% 6.84/7.07  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['30', '38'])).
% 6.84/7.07  thf('44', plain,
% 6.84/7.07      (![X1 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.84/7.07      inference('cnf', [status(esa)], [d3_tarski])).
% 6.84/7.07  thf(d4_xboole_0, axiom,
% 6.84/7.07    (![A:$i,B:$i,C:$i]:
% 6.84/7.07     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 6.84/7.07       ( ![D:$i]:
% 6.84/7.07         ( ( r2_hidden @ D @ C ) <=>
% 6.84/7.07           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 6.84/7.07  thf('45', plain,
% 6.84/7.07      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X8 @ X7)
% 6.84/7.07          | (r2_hidden @ X8 @ X6)
% 6.84/7.07          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 6.84/7.07      inference('cnf', [status(esa)], [d4_xboole_0])).
% 6.84/7.07  thf('46', plain,
% 6.84/7.07      (![X5 : $i, X6 : $i, X8 : $i]:
% 6.84/7.07         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.84/7.07      inference('simplify', [status(thm)], ['45'])).
% 6.84/7.07  thf('47', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 6.84/7.07          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['44', '46'])).
% 6.84/7.07  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.84/7.07      inference('simplify', [status(thm)], ['34'])).
% 6.84/7.07  thf('49', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 6.84/7.07      inference('sup-', [status(thm)], ['47', '48'])).
% 6.84/7.07  thf('50', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['39', '40'])).
% 6.84/7.07  thf('51', plain,
% 6.84/7.07      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['49', '50'])).
% 6.84/7.07  thf('52', plain,
% 6.84/7.07      (![X20 : $i, X21 : $i]:
% 6.84/7.07         ((k4_xboole_0 @ X20 @ X21)
% 6.84/7.07           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.84/7.07  thf('53', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['51', '52'])).
% 6.84/7.07  thf('54', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 6.84/7.07      inference('cnf', [status(esa)], [t5_boole])).
% 6.84/7.07  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.84/7.07      inference('demod', [status(thm)], ['53', '54'])).
% 6.84/7.07  thf('56', plain,
% 6.84/7.07      (![X28 : $i, X29 : $i]:
% 6.84/7.07         ((k2_xboole_0 @ X28 @ X29)
% 6.84/7.07           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.84/7.07  thf('57', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['55', '56'])).
% 6.84/7.07  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.84/7.07      inference('sup-', [status(thm)], ['31', '35'])).
% 6.84/7.07  thf('59', plain,
% 6.84/7.07      (![X22 : $i, X23 : $i]:
% 6.84/7.07         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 6.84/7.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.84/7.07  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['58', '59'])).
% 6.84/7.07  thf('61', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.84/7.07      inference('demod', [status(thm)], ['57', '60'])).
% 6.84/7.07  thf('62', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((X1) = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 6.84/7.07      inference('sup+', [status(thm)], ['43', '61'])).
% 6.84/7.07  thf('63', plain,
% 6.84/7.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 6.84/7.07           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.84/7.07  thf('64', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 6.84/7.07      inference('demod', [status(thm)], ['62', '63'])).
% 6.84/7.07  thf('65', plain,
% 6.84/7.07      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 6.84/7.07         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['42', '64'])).
% 6.84/7.07  thf('66', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 6.84/7.07      inference('cnf', [status(esa)], [t5_boole])).
% 6.84/7.07  thf('67', plain,
% 6.84/7.07      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 6.84/7.07         = (k1_tarski @ sk_A))),
% 6.84/7.07      inference('demod', [status(thm)], ['65', '66'])).
% 6.84/7.07  thf('68', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ~ (r2_hidden @ X2 @ 
% 6.84/7.07            (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 6.84/7.07      inference('sup-', [status(thm)], ['12', '23'])).
% 6.84/7.07  thf('69', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         ~ (r2_hidden @ X0 @ 
% 6.84/7.07            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 6.84/7.07      inference('sup-', [status(thm)], ['67', '68'])).
% 6.84/7.07  thf('70', plain,
% 6.84/7.07      (![X0 : $i]:
% 6.84/7.07         (r1_tarski @ 
% 6.84/7.07          (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07           (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 6.84/7.07          X0)),
% 6.84/7.07      inference('sup-', [status(thm)], ['0', '69'])).
% 6.84/7.07  thf('71', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['39', '40'])).
% 6.84/7.07  thf('72', plain,
% 6.84/7.07      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['70', '71'])).
% 6.84/7.07  thf('73', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 6.84/7.07      inference('demod', [status(thm)], ['62', '63'])).
% 6.84/7.07  thf('74', plain,
% 6.84/7.07      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 6.84/7.07         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07            k1_xboole_0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['72', '73'])).
% 6.84/7.07  thf('75', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 6.84/7.07      inference('cnf', [status(esa)], [t5_boole])).
% 6.84/7.07  thf('76', plain,
% 6.84/7.07      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 6.84/7.07         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 6.84/7.07      inference('demod', [status(thm)], ['74', '75'])).
% 6.84/7.07  thf('77', plain,
% 6.84/7.07      (![X1 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.84/7.07      inference('cnf', [status(esa)], [d3_tarski])).
% 6.84/7.07  thf('78', plain,
% 6.84/7.07      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X8 @ X7)
% 6.84/7.07          | (r2_hidden @ X8 @ X5)
% 6.84/7.07          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 6.84/7.07      inference('cnf', [status(esa)], [d4_xboole_0])).
% 6.84/7.07  thf('79', plain,
% 6.84/7.07      (![X5 : $i, X6 : $i, X8 : $i]:
% 6.84/7.07         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.84/7.07      inference('simplify', [status(thm)], ['78'])).
% 6.84/7.07  thf('80', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 6.84/7.07          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 6.84/7.07      inference('sup-', [status(thm)], ['77', '79'])).
% 6.84/7.07  thf('81', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 6.84/7.07          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['44', '46'])).
% 6.84/7.07  thf('82', plain,
% 6.84/7.07      (![X11 : $i, X12 : $i, X14 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X14 @ X12)
% 6.84/7.07          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 6.84/7.07      inference('simplify', [status(thm)], ['20'])).
% 6.84/7.07  thf('83', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.84/7.07         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 6.84/7.07          | ~ (r2_hidden @ 
% 6.84/7.07               (sk_C @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['81', '82'])).
% 6.84/7.07  thf('84', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 6.84/7.07          | (r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 6.84/7.07      inference('sup-', [status(thm)], ['80', '83'])).
% 6.84/7.07  thf('85', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         (r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 6.84/7.07      inference('simplify', [status(thm)], ['84'])).
% 6.84/7.07  thf('86', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['39', '40'])).
% 6.84/7.07  thf('87', plain,
% 6.84/7.07      (![X1 : $i, X2 : $i]:
% 6.84/7.07         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)) = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['85', '86'])).
% 6.84/7.07  thf('88', plain,
% 6.84/7.07      (![X20 : $i, X21 : $i]:
% 6.84/7.07         ((k4_xboole_0 @ X20 @ X21)
% 6.84/7.07           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.84/7.07  thf('89', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 6.84/7.07           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['87', '88'])).
% 6.84/7.07  thf('90', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 6.84/7.07      inference('cnf', [status(esa)], [t5_boole])).
% 6.84/7.07  thf('91', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 6.84/7.07      inference('demod', [status(thm)], ['89', '90'])).
% 6.84/7.07  thf('92', plain,
% 6.84/7.07      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 6.84/7.07         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A))),
% 6.84/7.07      inference('sup+', [status(thm)], ['76', '91'])).
% 6.84/7.07  thf('93', plain,
% 6.84/7.07      (![X28 : $i, X29 : $i]:
% 6.84/7.07         ((k2_xboole_0 @ X28 @ X29)
% 6.84/7.07           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.84/7.07  thf('94', plain,
% 6.84/7.07      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07         (k1_tarski @ sk_A))
% 6.84/7.07         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07            (k1_tarski @ sk_A)))),
% 6.84/7.07      inference('sup+', [status(thm)], ['92', '93'])).
% 6.84/7.07  thf('95', plain,
% 6.84/7.07      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 6.84/7.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.84/7.07  thf('96', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 6.84/7.07      inference('simplify', [status(thm)], ['95'])).
% 6.84/7.07  thf('97', plain,
% 6.84/7.07      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.84/7.07         ((r2_hidden @ X62 @ X61)
% 6.84/7.07          | ~ (r1_tarski @ (k2_tarski @ X60 @ X62) @ X61))),
% 6.84/7.07      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.84/7.07  thf('98', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['96', '97'])).
% 6.84/7.07  thf('99', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 6.84/7.07      inference('simplify', [status(thm)], ['95'])).
% 6.84/7.07  thf('100', plain,
% 6.84/7.07      (![X60 : $i, X61 : $i, X62 : $i]:
% 6.84/7.07         ((r2_hidden @ X60 @ X61)
% 6.84/7.07          | ~ (r1_tarski @ (k2_tarski @ X60 @ X62) @ X61))),
% 6.84/7.07      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.84/7.07  thf('101', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['99', '100'])).
% 6.84/7.07  thf('102', plain,
% 6.84/7.07      (![X60 : $i, X62 : $i, X63 : $i]:
% 6.84/7.07         ((r1_tarski @ (k2_tarski @ X60 @ X62) @ X63)
% 6.84/7.07          | ~ (r2_hidden @ X62 @ X63)
% 6.84/7.07          | ~ (r2_hidden @ X60 @ X63))),
% 6.84/7.07      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.84/7.07  thf('103', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 6.84/7.07          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['101', '102'])).
% 6.84/7.07  thf('104', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['98', '103'])).
% 6.84/7.07  thf('105', plain,
% 6.84/7.07      (![X17 : $i, X19 : $i]:
% 6.84/7.07         (((X17) = (X19))
% 6.84/7.07          | ~ (r1_tarski @ X19 @ X17)
% 6.84/7.07          | ~ (r1_tarski @ X17 @ X19))),
% 6.84/7.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.84/7.07  thf('106', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 6.84/7.07          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 6.84/7.07      inference('sup-', [status(thm)], ['104', '105'])).
% 6.84/7.07  thf('107', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['98', '103'])).
% 6.84/7.07  thf('108', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.84/7.07      inference('demod', [status(thm)], ['106', '107'])).
% 6.84/7.07  thf(l51_zfmisc_1, axiom,
% 6.84/7.07    (![A:$i,B:$i]:
% 6.84/7.07     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 6.84/7.07  thf('109', plain,
% 6.84/7.07      (![X58 : $i, X59 : $i]:
% 6.84/7.07         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 6.84/7.07      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 6.84/7.07  thf('110', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 6.84/7.07      inference('sup+', [status(thm)], ['108', '109'])).
% 6.84/7.07  thf('111', plain,
% 6.84/7.07      (![X58 : $i, X59 : $i]:
% 6.84/7.07         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 6.84/7.07      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 6.84/7.07  thf('112', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.84/7.07      inference('sup+', [status(thm)], ['110', '111'])).
% 6.84/7.07  thf('113', plain,
% 6.84/7.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 6.84/7.07           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.84/7.07  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.84/7.07      inference('sup-', [status(thm)], ['30', '38'])).
% 6.84/7.07  thf('115', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 6.84/7.07           = (k1_xboole_0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['113', '114'])).
% 6.84/7.07  thf('116', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 6.84/7.07      inference('demod', [status(thm)], ['62', '63'])).
% 6.84/7.07  thf('117', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 6.84/7.07           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['115', '116'])).
% 6.84/7.07  thf('118', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 6.84/7.07      inference('cnf', [status(esa)], [t5_boole])).
% 6.84/7.07  thf('119', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 6.84/7.07      inference('demod', [status(thm)], ['117', '118'])).
% 6.84/7.07  thf('120', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 6.84/7.07      inference('demod', [status(thm)], ['62', '63'])).
% 6.84/7.07  thf('121', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 6.84/7.07      inference('sup+', [status(thm)], ['119', '120'])).
% 6.84/7.07  thf('122', plain,
% 6.84/7.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 6.84/7.07           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 6.84/7.07      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.84/7.07  thf('123', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 6.84/7.07           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 6.84/7.07      inference('sup+', [status(thm)], ['121', '122'])).
% 6.84/7.07  thf('124', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]:
% 6.84/7.07         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 6.84/7.07      inference('demod', [status(thm)], ['117', '118'])).
% 6.84/7.07  thf('125', plain,
% 6.84/7.07      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 6.84/7.07         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B))),
% 6.84/7.07      inference('demod', [status(thm)], ['94', '112', '123', '124'])).
% 6.84/7.07  thf('126', plain,
% 6.84/7.07      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07         (k1_tarski @ sk_A)) != (sk_B))),
% 6.84/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.84/7.07  thf('127', plain,
% 6.84/7.07      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 6.84/7.07         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 6.84/7.07      inference('demod', [status(thm)], ['74', '75'])).
% 6.84/7.07  thf('128', plain,
% 6.84/7.07      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 6.84/7.07         (k1_tarski @ sk_A)) != (sk_B))),
% 6.84/7.07      inference('demod', [status(thm)], ['126', '127'])).
% 6.84/7.07  thf('129', plain,
% 6.84/7.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.84/7.07      inference('sup+', [status(thm)], ['110', '111'])).
% 6.84/7.07  thf('130', plain,
% 6.84/7.07      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 6.84/7.07         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 6.84/7.07      inference('demod', [status(thm)], ['128', '129'])).
% 6.84/7.07  thf('131', plain, ($false),
% 6.84/7.07      inference('simplify_reflect-', [status(thm)], ['125', '130'])).
% 6.84/7.07  
% 6.84/7.07  % SZS output end Refutation
% 6.84/7.07  
% 6.84/7.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
