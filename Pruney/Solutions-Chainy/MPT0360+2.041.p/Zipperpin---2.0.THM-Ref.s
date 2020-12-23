%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJni3dpDds

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:46 EST 2020

% Result     : Theorem 6.75s
% Output     : Refutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :  156 (1180 expanded)
%              Number of leaves         :   28 ( 363 expanded)
%              Depth                    :   21
%              Number of atoms          : 1213 (10456 expanded)
%              Number of equality atoms :   88 ( 854 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['18','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ X0 ) @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_C_1 ) @ sk_B )
    | ( sk_B
      = ( k4_xboole_0 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('64',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_C_1 ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','53','65'])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('70',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('75',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( ( k3_subset_1 @ sk_C_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('78',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( ( k3_subset_1 @ sk_C_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) )
      = ( k4_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_C_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ( m1_subset_1 @ X26 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('90',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ sk_C_1 @ ( k3_subset_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('94',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ( m1_subset_1 @ X26 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('95',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ sk_C_1 @ X0 )
        = ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('99',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','106'])).

thf('108',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('109',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ( m1_subset_1 @ X26 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('110',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['107','116'])).

thf('118',plain,
    ( ( k1_xboole_0 = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','117'])).

thf('119',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('120',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['118','123'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJni3dpDds
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.75/6.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.75/6.94  % Solved by: fo/fo7.sh
% 6.75/6.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.75/6.94  % done 6331 iterations in 6.478s
% 6.75/6.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.75/6.94  % SZS output start Refutation
% 6.75/6.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.75/6.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.75/6.94  thf(sk_A_type, type, sk_A: $i).
% 6.75/6.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.75/6.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.75/6.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.75/6.94  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.75/6.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.75/6.94  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.75/6.94  thf(sk_B_type, type, sk_B: $i).
% 6.75/6.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.75/6.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.75/6.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.75/6.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.75/6.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.75/6.94  thf(t40_subset_1, conjecture,
% 6.75/6.94    (![A:$i,B:$i,C:$i]:
% 6.75/6.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.75/6.94       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 6.75/6.94         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.75/6.94  thf(zf_stmt_0, negated_conjecture,
% 6.75/6.94    (~( ![A:$i,B:$i,C:$i]:
% 6.75/6.94        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.75/6.94          ( ( ( r1_tarski @ B @ C ) & 
% 6.75/6.94              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 6.75/6.94            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 6.75/6.94    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 6.75/6.94  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf(d5_subset_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.75/6.94       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 6.75/6.94  thf('2', plain,
% 6.75/6.94      (![X27 : $i, X28 : $i]:
% 6.75/6.94         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 6.75/6.94          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.75/6.94  thf('3', plain,
% 6.75/6.94      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['1', '2'])).
% 6.75/6.94  thf(t106_xboole_1, axiom,
% 6.75/6.94    (![A:$i,B:$i,C:$i]:
% 6.75/6.94     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.75/6.94       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.75/6.94  thf('4', plain,
% 6.75/6.94      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.75/6.94         ((r1_xboole_0 @ X8 @ X10)
% 6.75/6.94          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 6.75/6.94      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.75/6.94  thf('5', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 6.75/6.94          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['3', '4'])).
% 6.75/6.94  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 6.75/6.94      inference('sup-', [status(thm)], ['0', '5'])).
% 6.75/6.94  thf(t83_xboole_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.75/6.94  thf('7', plain,
% 6.75/6.94      (![X16 : $i, X17 : $i]:
% 6.75/6.94         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 6.75/6.94      inference('cnf', [status(esa)], [t83_xboole_1])).
% 6.75/6.94  thf('8', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 6.75/6.94      inference('sup-', [status(thm)], ['6', '7'])).
% 6.75/6.94  thf(d5_xboole_0, axiom,
% 6.75/6.94    (![A:$i,B:$i,C:$i]:
% 6.75/6.94     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 6.75/6.94       ( ![D:$i]:
% 6.75/6.94         ( ( r2_hidden @ D @ C ) <=>
% 6.75/6.94           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 6.75/6.94  thf('9', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X5 : $i]:
% 6.75/6.94         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('10', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X5 : $i]:
% 6.75/6.94         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('11', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X5 : $i]:
% 6.75/6.94         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 6.75/6.94          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('12', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 6.75/6.94          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 6.75/6.94          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['10', '11'])).
% 6.75/6.94  thf(t3_boole, axiom,
% 6.75/6.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.75/6.94  thf('13', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 6.75/6.94      inference('cnf', [status(esa)], [t3_boole])).
% 6.75/6.94  thf(t48_xboole_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.75/6.94  thf('14', plain,
% 6.75/6.94      (![X12 : $i, X13 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 6.75/6.94           = (k3_xboole_0 @ X12 @ X13))),
% 6.75/6.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.75/6.94  thf('15', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['13', '14'])).
% 6.75/6.94  thf('16', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['13', '14'])).
% 6.75/6.94  thf('17', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 6.75/6.94          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 6.75/6.94          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.75/6.94      inference('demod', [status(thm)], ['12', '15', '16'])).
% 6.75/6.94  thf('18', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 6.75/6.94      inference('simplify', [status(thm)], ['17'])).
% 6.75/6.94  thf('19', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X5 : $i]:
% 6.75/6.94         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('20', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 6.75/6.94      inference('cnf', [status(esa)], [t3_boole])).
% 6.75/6.94  thf('21', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X4 @ X3)
% 6.75/6.94          | ~ (r2_hidden @ X4 @ X2)
% 6.75/6.94          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('22', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X4 @ X2)
% 6.75/6.94          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['21'])).
% 6.75/6.94  thf('23', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 6.75/6.94      inference('sup-', [status(thm)], ['20', '22'])).
% 6.75/6.94  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.75/6.94      inference('condensation', [status(thm)], ['23'])).
% 6.75/6.94  thf('25', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 6.75/6.94          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['19', '24'])).
% 6.75/6.94  thf('26', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['13', '14'])).
% 6.75/6.94  thf('27', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X4 @ X3)
% 6.75/6.94          | (r2_hidden @ X4 @ X1)
% 6.75/6.94          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('28', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.75/6.94         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['27'])).
% 6.75/6.94  thf('29', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 6.75/6.94          | (r2_hidden @ X1 @ X0))),
% 6.75/6.94      inference('sup-', [status(thm)], ['26', '28'])).
% 6.75/6.94  thf('30', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['13', '14'])).
% 6.75/6.94  thf('31', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X4 @ X2)
% 6.75/6.94          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['21'])).
% 6.75/6.94  thf('32', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 6.75/6.94          | ~ (r2_hidden @ X1 @ X0))),
% 6.75/6.94      inference('sup-', [status(thm)], ['30', '31'])).
% 6.75/6.94  thf('33', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('clc', [status(thm)], ['29', '32'])).
% 6.75/6.94  thf('34', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['25', '33'])).
% 6.75/6.94  thf('35', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 6.75/6.94      inference('cnf', [status(esa)], [t3_boole])).
% 6.75/6.94  thf('36', plain,
% 6.75/6.94      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['34', '35'])).
% 6.75/6.94  thf('37', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 6.75/6.94      inference('demod', [status(thm)], ['18', '36'])).
% 6.75/6.94  thf('38', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 6.75/6.94      inference('sup-', [status(thm)], ['6', '7'])).
% 6.75/6.94  thf('39', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X4 @ X2)
% 6.75/6.94          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['21'])).
% 6.75/6.94  thf('40', plain,
% 6.75/6.94      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['38', '39'])).
% 6.75/6.94  thf('41', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (((sk_B) = (k1_xboole_0))
% 6.75/6.94          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ X0) @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['37', '40'])).
% 6.75/6.94  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf('43', plain,
% 6.75/6.94      (![X0 : $i]: ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ X0) @ sk_C_1)),
% 6.75/6.94      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 6.75/6.94  thf('44', plain,
% 6.75/6.94      (((r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_C_1) @ sk_B)
% 6.75/6.94        | ((sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_C_1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['9', '43'])).
% 6.75/6.94  thf('45', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['13', '14'])).
% 6.75/6.94  thf('46', plain,
% 6.75/6.94      (![X12 : $i, X13 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 6.75/6.94           = (k3_xboole_0 @ X12 @ X13))),
% 6.75/6.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.75/6.94  thf('47', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 6.75/6.94           = (k3_xboole_0 @ X0 @ X0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['45', '46'])).
% 6.75/6.94  thf('48', plain,
% 6.75/6.94      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['34', '35'])).
% 6.75/6.94  thf('49', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 6.75/6.94      inference('demod', [status(thm)], ['47', '48'])).
% 6.75/6.94  thf('50', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 6.75/6.94      inference('cnf', [status(esa)], [t3_boole])).
% 6.75/6.94  thf('51', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.75/6.94      inference('demod', [status(thm)], ['49', '50'])).
% 6.75/6.94  thf(t100_xboole_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.75/6.94  thf('52', plain,
% 6.75/6.94      (![X6 : $i, X7 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X6 @ X7)
% 6.75/6.94           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 6.75/6.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.75/6.94  thf('53', plain,
% 6.75/6.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['51', '52'])).
% 6.75/6.94  thf('54', plain,
% 6.75/6.94      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['34', '35'])).
% 6.75/6.94  thf('55', plain,
% 6.75/6.94      (![X12 : $i, X13 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 6.75/6.94           = (k3_xboole_0 @ X12 @ X13))),
% 6.75/6.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.75/6.94  thf('56', plain,
% 6.75/6.94      (![X6 : $i, X7 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X6 @ X7)
% 6.75/6.94           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 6.75/6.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.75/6.94  thf('57', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((k3_xboole_0 @ X1 @ X0)
% 6.75/6.94           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 6.75/6.94      inference('sup+', [status(thm)], ['55', '56'])).
% 6.75/6.94  thf('58', plain,
% 6.75/6.94      (![X12 : $i, X13 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 6.75/6.94           = (k3_xboole_0 @ X12 @ X13))),
% 6.75/6.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.75/6.94  thf('59', plain,
% 6.75/6.94      (![X12 : $i, X13 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 6.75/6.94           = (k3_xboole_0 @ X12 @ X13))),
% 6.75/6.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.75/6.94  thf('60', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 6.75/6.94           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.75/6.94      inference('sup+', [status(thm)], ['58', '59'])).
% 6.75/6.94  thf('61', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((k3_xboole_0 @ X1 @ X0)
% 6.75/6.94           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 6.75/6.94      inference('demod', [status(thm)], ['57', '60'])).
% 6.75/6.94  thf('62', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 6.75/6.94           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.75/6.94      inference('sup+', [status(thm)], ['54', '61'])).
% 6.75/6.94  thf('63', plain,
% 6.75/6.94      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['34', '35'])).
% 6.75/6.94  thf('64', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 6.75/6.94      inference('cnf', [status(esa)], [t3_boole])).
% 6.75/6.94  thf('65', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 6.75/6.94      inference('demod', [status(thm)], ['62', '63', '64'])).
% 6.75/6.94  thf('66', plain,
% 6.75/6.94      (((r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_C_1) @ sk_B)
% 6.75/6.94        | ((sk_B) = (k1_xboole_0)))),
% 6.75/6.94      inference('demod', [status(thm)], ['44', '53', '65'])).
% 6.75/6.94  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf('68', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_C_1) @ sk_B)),
% 6.75/6.94      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 6.75/6.94  thf('69', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf(d1_zfmisc_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 6.75/6.94       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 6.75/6.94  thf('70', plain,
% 6.75/6.94      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.75/6.94         (~ (r1_tarski @ X19 @ X20)
% 6.75/6.94          | (r2_hidden @ X19 @ X21)
% 6.75/6.94          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 6.75/6.94      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.75/6.94  thf('71', plain,
% 6.75/6.94      (![X19 : $i, X20 : $i]:
% 6.75/6.94         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 6.75/6.94      inference('simplify', [status(thm)], ['70'])).
% 6.75/6.94  thf('72', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['69', '71'])).
% 6.75/6.94  thf(d2_subset_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( ( v1_xboole_0 @ A ) =>
% 6.75/6.94         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.75/6.94       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.75/6.94         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.75/6.94  thf('73', plain,
% 6.75/6.94      (![X24 : $i, X25 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X24 @ X25)
% 6.75/6.94          | (m1_subset_1 @ X24 @ X25)
% 6.75/6.94          | (v1_xboole_0 @ X25))),
% 6.75/6.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.75/6.94  thf('74', plain,
% 6.75/6.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C_1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['72', '73'])).
% 6.75/6.94  thf(involutiveness_k3_subset_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.75/6.94       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 6.75/6.94  thf('75', plain,
% 6.75/6.94      (![X31 : $i, X32 : $i]:
% 6.75/6.94         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 6.75/6.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 6.75/6.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.75/6.94  thf('76', plain,
% 6.75/6.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94        | ((k3_subset_1 @ sk_C_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)) = (sk_B)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['74', '75'])).
% 6.75/6.94  thf('77', plain,
% 6.75/6.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C_1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['72', '73'])).
% 6.75/6.94  thf(dt_k3_subset_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.75/6.94       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.75/6.94  thf('78', plain,
% 6.75/6.94      (![X29 : $i, X30 : $i]:
% 6.75/6.94         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 6.75/6.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 6.75/6.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.75/6.94  thf('79', plain,
% 6.75/6.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94        | (m1_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_C_1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['77', '78'])).
% 6.75/6.94  thf('80', plain,
% 6.75/6.94      (![X27 : $i, X28 : $i]:
% 6.75/6.94         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 6.75/6.94          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.75/6.94  thf('81', plain,
% 6.75/6.94      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94        | ((k3_subset_1 @ sk_C_1 @ (k3_subset_1 @ sk_C_1 @ sk_B))
% 6.75/6.94            = (k4_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_C_1 @ sk_B))))),
% 6.75/6.94      inference('sup-', [status(thm)], ['79', '80'])).
% 6.75/6.94  thf('82', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.75/6.94         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['27'])).
% 6.75/6.94  thf('83', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X0 @ 
% 6.75/6.94             (k3_subset_1 @ sk_C_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 6.75/6.94          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94          | (r2_hidden @ X0 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['81', '82'])).
% 6.75/6.94  thf('84', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X0 @ sk_B)
% 6.75/6.94          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94          | (r2_hidden @ X0 @ sk_C_1)
% 6.75/6.94          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['76', '83'])).
% 6.75/6.94  thf('85', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         ((r2_hidden @ X0 @ sk_C_1)
% 6.75/6.94          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94          | ~ (r2_hidden @ X0 @ sk_B))),
% 6.75/6.94      inference('simplify', [status(thm)], ['84'])).
% 6.75/6.94  thf('86', plain,
% 6.75/6.94      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['38', '39'])).
% 6.75/6.94  thf('87', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (r2_hidden @ X0 @ sk_B) | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1)))),
% 6.75/6.94      inference('clc', [status(thm)], ['85', '86'])).
% 6.75/6.94  thf('88', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['68', '87'])).
% 6.75/6.94  thf('89', plain,
% 6.75/6.94      (![X25 : $i, X26 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ X26)
% 6.75/6.94          | (m1_subset_1 @ X26 @ X25)
% 6.75/6.94          | ~ (v1_xboole_0 @ X25))),
% 6.75/6.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.75/6.94  thf('90', plain,
% 6.75/6.94      (![X31 : $i, X32 : $i]:
% 6.75/6.94         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 6.75/6.94          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 6.75/6.94      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.75/6.94  thf('91', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 6.75/6.94          | ~ (v1_xboole_0 @ X1)
% 6.75/6.94          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['89', '90'])).
% 6.75/6.94  thf('92', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (((k3_subset_1 @ sk_C_1 @ (k3_subset_1 @ sk_C_1 @ X0)) = (X0))
% 6.75/6.94          | ~ (v1_xboole_0 @ X0))),
% 6.75/6.94      inference('sup-', [status(thm)], ['88', '91'])).
% 6.75/6.94  thf('93', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['68', '87'])).
% 6.75/6.94  thf('94', plain,
% 6.75/6.94      (![X25 : $i, X26 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ X26)
% 6.75/6.94          | (m1_subset_1 @ X26 @ X25)
% 6.75/6.94          | ~ (v1_xboole_0 @ X25))),
% 6.75/6.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.75/6.94  thf('95', plain,
% 6.75/6.94      (![X27 : $i, X28 : $i]:
% 6.75/6.94         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 6.75/6.94          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.75/6.94  thf('96', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 6.75/6.94          | ~ (v1_xboole_0 @ X1)
% 6.75/6.94          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['94', '95'])).
% 6.75/6.94  thf('97', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (((k3_subset_1 @ sk_C_1 @ X0) = (k4_xboole_0 @ sk_C_1 @ X0))
% 6.75/6.94          | ~ (v1_xboole_0 @ X0))),
% 6.75/6.94      inference('sup-', [status(thm)], ['93', '96'])).
% 6.75/6.94  thf('98', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X5 : $i]:
% 6.75/6.94         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('99', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.75/6.94         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['27'])).
% 6.75/6.94  thf('100', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.75/6.94         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 6.75/6.94          | ((X3) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['98', '99'])).
% 6.75/6.94  thf('101', plain,
% 6.75/6.94      (![X1 : $i, X2 : $i, X5 : $i]:
% 6.75/6.94         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 6.75/6.94          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 6.75/6.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.75/6.94  thf('102', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.75/6.94         (((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 6.75/6.94          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 6.75/6.94          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 6.75/6.94          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['100', '101'])).
% 6.75/6.94  thf('103', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.75/6.94         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 6.75/6.94          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 6.75/6.94      inference('simplify', [status(thm)], ['102'])).
% 6.75/6.94  thf('104', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.75/6.94      inference('condensation', [status(thm)], ['23'])).
% 6.75/6.94  thf('105', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['103', '104'])).
% 6.75/6.94  thf('106', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (((k1_xboole_0) = (k4_xboole_0 @ (k3_subset_1 @ sk_C_1 @ X0) @ sk_C_1))
% 6.75/6.94          | ~ (v1_xboole_0 @ X0))),
% 6.75/6.94      inference('sup+', [status(thm)], ['97', '105'])).
% 6.75/6.94  thf('107', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ sk_C_1))
% 6.75/6.94          | ~ (v1_xboole_0 @ X0)
% 6.75/6.94          | ~ (v1_xboole_0 @ (k3_subset_1 @ sk_C_1 @ X0)))),
% 6.75/6.94      inference('sup+', [status(thm)], ['92', '106'])).
% 6.75/6.94  thf('108', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['68', '87'])).
% 6.75/6.94  thf('109', plain,
% 6.75/6.94      (![X25 : $i, X26 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ X26)
% 6.75/6.94          | (m1_subset_1 @ X26 @ X25)
% 6.75/6.94          | ~ (v1_xboole_0 @ X25))),
% 6.75/6.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.75/6.94  thf('110', plain,
% 6.75/6.94      (![X29 : $i, X30 : $i]:
% 6.75/6.94         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 6.75/6.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 6.75/6.94      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.75/6.94  thf('111', plain,
% 6.75/6.94      (![X0 : $i, X1 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 6.75/6.94          | ~ (v1_xboole_0 @ X1)
% 6.75/6.94          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['109', '110'])).
% 6.75/6.94  thf('112', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         ((m1_subset_1 @ (k3_subset_1 @ sk_C_1 @ X0) @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94          | ~ (v1_xboole_0 @ X0))),
% 6.75/6.94      inference('sup-', [status(thm)], ['108', '111'])).
% 6.75/6.94  thf('113', plain,
% 6.75/6.94      (![X25 : $i, X26 : $i]:
% 6.75/6.94         (~ (m1_subset_1 @ X26 @ X25)
% 6.75/6.94          | (v1_xboole_0 @ X26)
% 6.75/6.94          | ~ (v1_xboole_0 @ X25))),
% 6.75/6.94      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.75/6.94  thf('114', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ X0)
% 6.75/6.94          | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 6.75/6.94          | (v1_xboole_0 @ (k3_subset_1 @ sk_C_1 @ X0)))),
% 6.75/6.94      inference('sup-', [status(thm)], ['112', '113'])).
% 6.75/6.94  thf('115', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['68', '87'])).
% 6.75/6.94  thf('116', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_subset_1 @ sk_C_1 @ X0)))),
% 6.75/6.94      inference('demod', [status(thm)], ['114', '115'])).
% 6.75/6.94  thf('117', plain,
% 6.75/6.94      (![X0 : $i]:
% 6.75/6.94         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ sk_C_1)))),
% 6.75/6.94      inference('clc', [status(thm)], ['107', '116'])).
% 6.75/6.94  thf('118', plain, ((((k1_xboole_0) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 6.75/6.94      inference('sup+', [status(thm)], ['8', '117'])).
% 6.75/6.94  thf('119', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 6.75/6.94      inference('sup-', [status(thm)], ['0', '5'])).
% 6.75/6.94  thf(t69_xboole_1, axiom,
% 6.75/6.94    (![A:$i,B:$i]:
% 6.75/6.94     ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.75/6.94       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 6.75/6.94  thf('120', plain,
% 6.75/6.94      (![X14 : $i, X15 : $i]:
% 6.75/6.94         (~ (r1_xboole_0 @ X14 @ X15)
% 6.75/6.94          | ~ (r1_tarski @ X14 @ X15)
% 6.75/6.94          | (v1_xboole_0 @ X14))),
% 6.75/6.94      inference('cnf', [status(esa)], [t69_xboole_1])).
% 6.75/6.94  thf('121', plain, (((v1_xboole_0 @ sk_B) | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 6.75/6.94      inference('sup-', [status(thm)], ['119', '120'])).
% 6.75/6.94  thf('122', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf('123', plain, ((v1_xboole_0 @ sk_B)),
% 6.75/6.94      inference('demod', [status(thm)], ['121', '122'])).
% 6.75/6.94  thf('124', plain, (((k1_xboole_0) = (sk_B))),
% 6.75/6.94      inference('demod', [status(thm)], ['118', '123'])).
% 6.75/6.94  thf('125', plain, (((sk_B) != (k1_xboole_0))),
% 6.75/6.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.75/6.94  thf('126', plain, ($false),
% 6.75/6.94      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 6.75/6.94  
% 6.75/6.94  % SZS output end Refutation
% 6.75/6.94  
% 6.75/6.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
