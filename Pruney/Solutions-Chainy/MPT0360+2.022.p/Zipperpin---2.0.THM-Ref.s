%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7FAVyGoutF

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 2.94s
% Output     : Refutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  147 (3379 expanded)
%              Number of leaves         :   20 (1006 expanded)
%              Depth                    :   22
%              Number of atoms          : 1379 (29837 expanded)
%              Number of equality atoms :  103 (2517 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('30',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','31'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X0 )
      | ( X0
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X0 )
      | ( X0
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('58',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['45','63'])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( X2
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(condensation,[status(thm)],['70'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('80',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['82','88'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','81'])).

thf('91',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf('93',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( k1_xboole_0 = sk_B ) ),
    inference(demod,[status(thm)],['89','90','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('104',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('105',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('115',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','80'])).

thf('117',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('119',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['115','116'])).

thf('121',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('122',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C )
    | ( k1_xboole_0 = sk_B ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['108','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7FAVyGoutF
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:08:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.94/3.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.94/3.12  % Solved by: fo/fo7.sh
% 2.94/3.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.94/3.12  % done 4132 iterations in 2.674s
% 2.94/3.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.94/3.12  % SZS output start Refutation
% 2.94/3.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.94/3.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.94/3.12  thf(sk_B_type, type, sk_B: $i).
% 2.94/3.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.94/3.12  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.94/3.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.94/3.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.94/3.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.94/3.12  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.94/3.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.94/3.12  thf(sk_A_type, type, sk_A: $i).
% 2.94/3.12  thf(sk_C_type, type, sk_C: $i).
% 2.94/3.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.94/3.12  thf(t40_subset_1, conjecture,
% 2.94/3.12    (![A:$i,B:$i,C:$i]:
% 2.94/3.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.94/3.13       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 2.94/3.13         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.94/3.13  thf(zf_stmt_0, negated_conjecture,
% 2.94/3.13    (~( ![A:$i,B:$i,C:$i]:
% 2.94/3.13        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.94/3.13          ( ( ( r1_tarski @ B @ C ) & 
% 2.94/3.13              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 2.94/3.13            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 2.94/3.13    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 2.94/3.13  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 2.94/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.94/3.13  thf(t28_xboole_1, axiom,
% 2.94/3.13    (![A:$i,B:$i]:
% 2.94/3.13     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.94/3.13  thf('1', plain,
% 2.94/3.13      (![X11 : $i, X12 : $i]:
% 2.94/3.13         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 2.94/3.13      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.94/3.13  thf('2', plain,
% 2.94/3.13      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_B))),
% 2.94/3.13      inference('sup-', [status(thm)], ['0', '1'])).
% 2.94/3.13  thf(t100_xboole_1, axiom,
% 2.94/3.13    (![A:$i,B:$i]:
% 2.94/3.13     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.94/3.13  thf('3', plain,
% 2.94/3.13      (![X9 : $i, X10 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ X9 @ X10)
% 2.94/3.13           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.94/3.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.94/3.13  thf('4', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 2.94/3.13         = (k5_xboole_0 @ sk_B @ sk_B))),
% 2.94/3.13      inference('sup+', [status(thm)], ['2', '3'])).
% 2.94/3.13  thf(d5_xboole_0, axiom,
% 2.94/3.13    (![A:$i,B:$i,C:$i]:
% 2.94/3.13     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.94/3.13       ( ![D:$i]:
% 2.94/3.13         ( ( r2_hidden @ D @ C ) <=>
% 2.94/3.13           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.94/3.13  thf('5', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('6', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 2.94/3.13         = (k5_xboole_0 @ sk_B @ sk_B))),
% 2.94/3.13      inference('sup+', [status(thm)], ['2', '3'])).
% 2.94/3.13  thf('7', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X4 @ X3)
% 2.94/3.13          | (r2_hidden @ X4 @ X1)
% 2.94/3.13          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('8', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.94/3.13         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['7'])).
% 2.94/3.13  thf('9', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ sk_B))
% 2.94/3.13          | (r2_hidden @ X0 @ sk_B))),
% 2.94/3.13      inference('sup-', [status(thm)], ['6', '8'])).
% 2.94/3.13  thf(d10_xboole_0, axiom,
% 2.94/3.13    (![A:$i,B:$i]:
% 2.94/3.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.94/3.13  thf('10', plain,
% 2.94/3.13      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 2.94/3.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.94/3.13  thf('11', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.94/3.13      inference('simplify', [status(thm)], ['10'])).
% 2.94/3.13  thf('12', plain,
% 2.94/3.13      (![X11 : $i, X12 : $i]:
% 2.94/3.13         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 2.94/3.13      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.94/3.13  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['11', '12'])).
% 2.94/3.13  thf('14', plain,
% 2.94/3.13      (![X9 : $i, X10 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ X9 @ X10)
% 2.94/3.13           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.94/3.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.94/3.13  thf('15', plain,
% 2.94/3.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.94/3.13      inference('sup+', [status(thm)], ['13', '14'])).
% 2.94/3.13  thf('16', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X4 @ X3)
% 2.94/3.13          | ~ (r2_hidden @ X4 @ X2)
% 2.94/3.13          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('17', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X4 @ X2)
% 2.94/3.13          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['16'])).
% 2.94/3.13  thf('18', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 2.94/3.13          | ~ (r2_hidden @ X1 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['15', '17'])).
% 2.94/3.13  thf('19', plain,
% 2.94/3.13      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ sk_B))),
% 2.94/3.13      inference('clc', [status(thm)], ['9', '18'])).
% 2.94/3.13  thf('20', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X1 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X1)
% 2.94/3.13          | ((X1) = (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ X0)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['5', '19'])).
% 2.94/3.13  thf('21', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X1 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X1)
% 2.94/3.13          | ((X1) = (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ X0)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['5', '19'])).
% 2.94/3.13  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.94/3.13  thf('22', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 2.94/3.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.94/3.13  thf('23', plain,
% 2.94/3.13      (![X11 : $i, X12 : $i]:
% 2.94/3.13         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 2.94/3.13      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.94/3.13  thf('24', plain,
% 2.94/3.13      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['22', '23'])).
% 2.94/3.13  thf('25', plain,
% 2.94/3.13      (![X9 : $i, X10 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ X9 @ X10)
% 2.94/3.13           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.94/3.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.94/3.13  thf('26', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 2.94/3.13           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup+', [status(thm)], ['24', '25'])).
% 2.94/3.13  thf('27', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.94/3.13         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['7'])).
% 2.94/3.13  thf('28', plain,
% 2.94/3.13      (![X1 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 2.94/3.13          | (r2_hidden @ X1 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['26', '27'])).
% 2.94/3.13  thf('29', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 2.94/3.13          | ~ (r2_hidden @ X1 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['15', '17'])).
% 2.94/3.13  thf('30', plain,
% 2.94/3.13      (![X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('clc', [status(thm)], ['28', '29'])).
% 2.94/3.13  thf('31', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 2.94/3.13           = (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['21', '30'])).
% 2.94/3.13  thf('32', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X1 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X1)
% 2.94/3.13          | ((X1) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.94/3.13      inference('demod', [status(thm)], ['20', '31'])).
% 2.94/3.13  thf('33', plain,
% 2.94/3.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.94/3.13      inference('sup+', [status(thm)], ['13', '14'])).
% 2.94/3.13  thf('34', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.94/3.13         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['7'])).
% 2.94/3.13  thf('35', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['33', '34'])).
% 2.94/3.13  thf('36', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 2.94/3.13          | ~ (r2_hidden @ X1 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['15', '17'])).
% 2.94/3.13  thf('37', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 2.94/3.13      inference('clc', [status(thm)], ['35', '36'])).
% 2.94/3.13  thf('38', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['32', '37'])).
% 2.94/3.13  thf('39', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 2.94/3.13         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('demod', [status(thm)], ['4', '38'])).
% 2.94/3.13  thf('40', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('41', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.94/3.13         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['7'])).
% 2.94/3.13  thf('42', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 2.94/3.13          | ((X3) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.94/3.13      inference('sup-', [status(thm)], ['40', '41'])).
% 2.94/3.13  thf('43', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('44', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         (((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['42', '43'])).
% 2.94/3.13  thf('45', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['44'])).
% 2.94/3.13  thf('46', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['32', '37'])).
% 2.94/3.13  thf('47', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 2.94/3.13           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup+', [status(thm)], ['24', '25'])).
% 2.94/3.13  thf('48', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 2.94/3.13      inference('sup+', [status(thm)], ['46', '47'])).
% 2.94/3.13  thf('49', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X1 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X1)
% 2.94/3.13          | ((X1) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.94/3.13      inference('demod', [status(thm)], ['20', '31'])).
% 2.94/3.13  thf('50', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('51', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         (((X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X0)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ X0)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['49', '50'])).
% 2.94/3.13  thf('52', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 2.94/3.13           = (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['21', '30'])).
% 2.94/3.13  thf('53', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         (((X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X0)
% 2.94/3.13          | ((X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.94/3.13      inference('demod', [status(thm)], ['51', '52'])).
% 2.94/3.13  thf('54', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) @ X0)
% 2.94/3.13          | ((X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['53'])).
% 2.94/3.13  thf('55', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X1 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)) @ X1)
% 2.94/3.13          | ((X1) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.94/3.13      inference('sup+', [status(thm)], ['48', '54'])).
% 2.94/3.13  thf('56', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['44'])).
% 2.94/3.13  thf('57', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 2.94/3.13           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup+', [status(thm)], ['24', '25'])).
% 2.94/3.13  thf('58', plain,
% 2.94/3.13      (![X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('clc', [status(thm)], ['28', '29'])).
% 2.94/3.13  thf('59', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['57', '58'])).
% 2.94/3.13  thf('60', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 2.94/3.13           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X2))),
% 2.94/3.13      inference('sup-', [status(thm)], ['56', '59'])).
% 2.94/3.13  thf('61', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['57', '58'])).
% 2.94/3.13  thf('62', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['60', '61'])).
% 2.94/3.13  thf('63', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 2.94/3.13           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['55', '62'])).
% 2.94/3.13  thf('64', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 2.94/3.13          | ((X2) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.94/3.13      inference('demod', [status(thm)], ['45', '63'])).
% 2.94/3.13  thf('65', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('66', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X0 @ X1)
% 2.94/3.13          | (r2_hidden @ X0 @ X2)
% 2.94/3.13          | (r2_hidden @ X0 @ X3)
% 2.94/3.13          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('67', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ X0 @ X2)
% 2.94/3.13          | ~ (r2_hidden @ X0 @ X1))),
% 2.94/3.13      inference('simplify', [status(thm)], ['66'])).
% 2.94/3.13  thf('68', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ X0 @ X1))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X3)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['65', '67'])).
% 2.94/3.13  thf('69', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['57', '58'])).
% 2.94/3.13  thf('70', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ X1 @ k1_xboole_0) @ X0)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ k1_xboole_0 @ X1))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X1 @ k1_xboole_0) @ X2))),
% 2.94/3.13      inference('sup-', [status(thm)], ['68', '69'])).
% 2.94/3.13  thf('71', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ X0)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ k1_xboole_0 @ X1)))),
% 2.94/3.13      inference('condensation', [status(thm)], ['70'])).
% 2.94/3.13  thf('72', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('73', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 2.94/3.13               k1_xboole_0)
% 2.94/3.13          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 2.94/3.13          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['71', '72'])).
% 2.94/3.13  thf('74', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 2.94/3.13               k1_xboole_0)
% 2.94/3.13          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['73'])).
% 2.94/3.13  thf('75', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ X0)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ k1_xboole_0 @ X1)))),
% 2.94/3.13      inference('condensation', [status(thm)], ['70'])).
% 2.94/3.13  thf('76', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 2.94/3.13          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 2.94/3.13      inference('clc', [status(thm)], ['74', '75'])).
% 2.94/3.13  thf('77', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['57', '58'])).
% 2.94/3.13  thf('78', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k1_xboole_0)
% 2.94/3.13           = (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['76', '77'])).
% 2.94/3.13  thf('79', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['57', '58'])).
% 2.94/3.13  thf('80', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.94/3.13      inference('sup-', [status(thm)], ['78', '79'])).
% 2.94/3.13  thf('81', plain,
% 2.94/3.13      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['64', '80'])).
% 2.94/3.13  thf('82', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 2.94/3.13      inference('demod', [status(thm)], ['39', '81'])).
% 2.94/3.13  thf('83', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ X0 @ X1))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X3)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['65', '67'])).
% 2.94/3.13  thf('84', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('85', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.94/3.13      inference('sup-', [status(thm)], ['83', '84'])).
% 2.94/3.13  thf('86', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 2.94/3.13          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 2.94/3.13      inference('simplify', [status(thm)], ['85'])).
% 2.94/3.13  thf('87', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.94/3.13      inference('sup-', [status(thm)], ['78', '79'])).
% 2.94/3.13  thf('88', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) @ X1)
% 2.94/3.13          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 2.94/3.13      inference('sup-', [status(thm)], ['86', '87'])).
% 2.94/3.13  thf('89', plain,
% 2.94/3.13      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ 
% 2.94/3.13         (k3_subset_1 @ sk_A @ sk_C))
% 2.94/3.13        | ((k1_xboole_0)
% 2.94/3.13            = (k4_xboole_0 @ sk_B @ 
% 2.94/3.13               (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))))),
% 2.94/3.13      inference('sup+', [status(thm)], ['82', '88'])).
% 2.94/3.13  thf('90', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 2.94/3.13      inference('demod', [status(thm)], ['39', '81'])).
% 2.94/3.13  thf('91', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('92', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.94/3.13      inference('eq_fact', [status(thm)], ['91'])).
% 2.94/3.13  thf('93', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.94/3.13         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.94/3.13  thf('94', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.94/3.13          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.94/3.13      inference('sup-', [status(thm)], ['92', '93'])).
% 2.94/3.13  thf('95', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 2.94/3.13          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['94'])).
% 2.94/3.13  thf('96', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.94/3.13          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.94/3.13      inference('eq_fact', [status(thm)], ['91'])).
% 2.94/3.13  thf('97', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 2.94/3.13          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 2.94/3.13      inference('clc', [status(thm)], ['95', '96'])).
% 2.94/3.13  thf('98', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.94/3.13      inference('sup-', [status(thm)], ['78', '79'])).
% 2.94/3.13  thf('99', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['97', '98'])).
% 2.94/3.13  thf('100', plain,
% 2.94/3.13      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ 
% 2.94/3.13         (k3_subset_1 @ sk_A @ sk_C))
% 2.94/3.13        | ((k1_xboole_0) = (sk_B)))),
% 2.94/3.13      inference('demod', [status(thm)], ['89', '90', '99'])).
% 2.94/3.13  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 2.94/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.94/3.13  thf('102', plain,
% 2.94/3.13      ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ 
% 2.94/3.13        (k3_subset_1 @ sk_A @ sk_C))),
% 2.94/3.13      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 2.94/3.13  thf('103', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.94/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.94/3.13  thf(d5_subset_1, axiom,
% 2.94/3.13    (![A:$i,B:$i]:
% 2.94/3.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.94/3.13       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.94/3.13  thf('104', plain,
% 2.94/3.13      (![X14 : $i, X15 : $i]:
% 2.94/3.13         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 2.94/3.13          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 2.94/3.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.94/3.13  thf('105', plain,
% 2.94/3.13      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 2.94/3.13      inference('sup-', [status(thm)], ['103', '104'])).
% 2.94/3.13  thf('106', plain,
% 2.94/3.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X4 @ X2)
% 2.94/3.13          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.94/3.13      inference('simplify', [status(thm)], ['16'])).
% 2.94/3.13  thf('107', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 2.94/3.13          | ~ (r2_hidden @ X0 @ sk_C))),
% 2.94/3.13      inference('sup-', [status(thm)], ['105', '106'])).
% 2.94/3.13  thf('108', plain,
% 2.94/3.13      (~ (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C)),
% 2.94/3.13      inference('sup-', [status(thm)], ['102', '107'])).
% 2.94/3.13  thf('109', plain, ((r1_tarski @ sk_B @ sk_C)),
% 2.94/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.94/3.13  thf('110', plain,
% 2.94/3.13      (![X11 : $i, X12 : $i]:
% 2.94/3.13         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 2.94/3.13      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.94/3.13  thf('111', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 2.94/3.13      inference('sup-', [status(thm)], ['109', '110'])).
% 2.94/3.13  thf('112', plain,
% 2.94/3.13      (![X9 : $i, X10 : $i]:
% 2.94/3.13         ((k4_xboole_0 @ X9 @ X10)
% 2.94/3.13           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.94/3.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.94/3.13  thf('113', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ sk_B))),
% 2.94/3.13      inference('sup+', [status(thm)], ['111', '112'])).
% 2.94/3.13  thf('114', plain,
% 2.94/3.13      (![X0 : $i]:
% 2.94/3.13         ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['32', '37'])).
% 2.94/3.13  thf('115', plain,
% 2.94/3.13      (((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('demod', [status(thm)], ['113', '114'])).
% 2.94/3.13  thf('116', plain,
% 2.94/3.13      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['64', '80'])).
% 2.94/3.13  thf('117', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 2.94/3.13      inference('demod', [status(thm)], ['115', '116'])).
% 2.94/3.13  thf('118', plain,
% 2.94/3.13      (![X0 : $i, X1 : $i]:
% 2.94/3.13         ((r2_hidden @ (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) @ X1)
% 2.94/3.13          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 2.94/3.13      inference('sup-', [status(thm)], ['86', '87'])).
% 2.94/3.13  thf('119', plain,
% 2.94/3.13      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C)
% 2.94/3.13        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.94/3.13      inference('sup+', [status(thm)], ['117', '118'])).
% 2.94/3.13  thf('120', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 2.94/3.13      inference('demod', [status(thm)], ['115', '116'])).
% 2.94/3.13  thf('121', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 2.94/3.13      inference('sup-', [status(thm)], ['97', '98'])).
% 2.94/3.13  thf('122', plain,
% 2.94/3.13      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C)
% 2.94/3.13        | ((k1_xboole_0) = (sk_B)))),
% 2.94/3.13      inference('demod', [status(thm)], ['119', '120', '121'])).
% 2.94/3.13  thf('123', plain, (((sk_B) != (k1_xboole_0))),
% 2.94/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.94/3.13  thf('124', plain,
% 2.94/3.13      ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_C)),
% 2.94/3.13      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 2.94/3.13  thf('125', plain, ($false), inference('demod', [status(thm)], ['108', '124'])).
% 2.94/3.13  
% 2.94/3.13  % SZS output end Refutation
% 2.94/3.13  
% 2.94/3.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
