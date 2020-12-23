%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A4H2SQNYU0

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:07 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 316 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   24
%              Number of atoms          :  618 (3068 expanded)
%              Number of equality atoms :   28 ( 109 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('0',plain,(
    sk_B_2 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_C_3 )
      | ( r2_hidden @ X22 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_3 ) @ sk_B_2 )
    | ~ ( r2_hidden @ ( sk_B_1 @ sk_C_3 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_C_3 ) @ sk_B_2 )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_C_3 )
      | ( r2_hidden @ X22 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_B_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_B_2 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ( r1_tarski @ sk_C_3 @ sk_B_2 )
    | ( r1_tarski @ sk_C_3 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_C_3 @ sk_B_2 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('42',plain,(
    r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('44',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X13 @ X14 ) @ X14 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('46',plain,
    ( ( sk_B_2 = sk_C_3 )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B_2 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B_2 )
      | ( r2_hidden @ X22 @ sk_C_3 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_C_3 )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_C_3 ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_2 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X14 ) @ X13 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( sk_B_2 = sk_C_3 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2 = sk_C_3 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B_2 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','66'])).

thf('68',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','67'])).

thf('69',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A4H2SQNYU0
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 485 iterations in 0.239s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.70  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.49/0.70  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.49/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.70  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.49/0.70  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.49/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.70  thf(t44_setfam_1, conjecture,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.70       ( ![C:$i]:
% 0.49/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.70           ( ( ![D:$i]:
% 0.49/0.70               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.70                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.49/0.70             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i,B:$i]:
% 0.49/0.70        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.70          ( ![C:$i]:
% 0.49/0.70            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.70              ( ( ![D:$i]:
% 0.49/0.70                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.70                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.49/0.70                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.49/0.70  thf('0', plain, (((sk_B_2) != (sk_C_3))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(t7_xboole_0, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.49/0.70          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(t2_subset, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ A @ B ) =>
% 0.49/0.70       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      (![X17 : $i, X18 : $i]:
% 0.49/0.70         ((r2_hidden @ X17 @ X18)
% 0.49/0.70          | (v1_xboole_0 @ X18)
% 0.49/0.70          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.49/0.70      inference('cnf', [status(esa)], [t2_subset])).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.49/0.70        | (r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.70  thf(d1_zfmisc_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.49/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X11 @ X10)
% 0.49/0.70          | (r1_tarski @ X11 @ X9)
% 0.49/0.70          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X9 : $i, X11 : $i]:
% 0.49/0.70         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.49/0.70        | (r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['4', '6'])).
% 0.49/0.70  thf(d3_tarski, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.49/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (![X4 : $i, X6 : $i]:
% 0.49/0.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (![X4 : $i, X6 : $i]:
% 0.49/0.70         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('10', plain,
% 0.49/0.70      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.70  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.70      inference('simplify', [status(thm)], ['10'])).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.70         (~ (r1_tarski @ X8 @ X9)
% 0.49/0.70          | (r2_hidden @ X8 @ X10)
% 0.49/0.70          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.49/0.70  thf('13', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i]:
% 0.49/0.70         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.49/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.49/0.70  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['11', '13'])).
% 0.49/0.70  thf(d1_xboole_0, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.70  thf('16', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.49/0.70  thf('17', plain, ((r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.70      inference('clc', [status(thm)], ['7', '16'])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X3 @ X4)
% 0.49/0.70          | (r2_hidden @ X3 @ X5)
% 0.49/0.70          | ~ (r1_tarski @ X4 @ X5))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.70  thf('20', plain,
% 0.49/0.70      ((((sk_C_3) = (k1_xboole_0))
% 0.49/0.70        | (r2_hidden @ (sk_B_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['1', '19'])).
% 0.49/0.70  thf(t1_subset, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      (![X15 : $i, X16 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.49/0.70      inference('cnf', [status(esa)], [t1_subset])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      ((((sk_C_3) = (k1_xboole_0))
% 0.49/0.70        | (m1_subset_1 @ (sk_B_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (![X22 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X22 @ sk_C_3)
% 0.49/0.70          | (r2_hidden @ X22 @ sk_B_2)
% 0.49/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      ((((sk_C_3) = (k1_xboole_0))
% 0.49/0.70        | (r2_hidden @ (sk_B_1 @ sk_C_3) @ sk_B_2)
% 0.49/0.70        | ~ (r2_hidden @ (sk_B_1 @ sk_C_3) @ sk_C_3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.49/0.70  thf('25', plain,
% 0.49/0.70      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (((r2_hidden @ (sk_B_1 @ sk_C_3) @ sk_B_2) | ((sk_C_3) = (k1_xboole_0)))),
% 0.49/0.70      inference('clc', [status(thm)], ['24', '25'])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.70  thf('28', plain, ((((sk_C_3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (![X4 : $i, X6 : $i]:
% 0.49/0.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('30', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(t4_subset, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.49/0.70       ( m1_subset_1 @ A @ C ) ))).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X19 @ X20)
% 0.49/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.49/0.70          | (m1_subset_1 @ X19 @ X21))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset])).
% 0.49/0.70  thf('32', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.70          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r1_tarski @ sk_C_3 @ X0)
% 0.49/0.70          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['29', '32'])).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X22 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X22 @ sk_C_3)
% 0.49/0.70          | (r2_hidden @ X22 @ sk_B_2)
% 0.49/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r1_tarski @ sk_C_3 @ X0)
% 0.49/0.70          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_B_2)
% 0.49/0.70          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_C_3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('36', plain,
% 0.49/0.70      (![X4 : $i, X6 : $i]:
% 0.49/0.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('37', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_B_2)
% 0.49/0.70          | (r1_tarski @ sk_C_3 @ X0))),
% 0.49/0.70      inference('clc', [status(thm)], ['35', '36'])).
% 0.49/0.70  thf('38', plain,
% 0.49/0.70      (![X4 : $i, X6 : $i]:
% 0.49/0.70         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('39', plain,
% 0.49/0.70      (((r1_tarski @ sk_C_3 @ sk_B_2) | (r1_tarski @ sk_C_3 @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.70  thf('40', plain, ((r1_tarski @ sk_C_3 @ sk_B_2)),
% 0.49/0.70      inference('simplify', [status(thm)], ['39'])).
% 0.49/0.70  thf('41', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i]:
% 0.49/0.70         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.49/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.49/0.70  thf('42', plain, ((r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.70  thf('43', plain,
% 0.49/0.70      (![X15 : $i, X16 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.49/0.70      inference('cnf', [status(esa)], [t1_subset])).
% 0.49/0.70  thf('44', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.70  thf(t49_subset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.70       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.49/0.70         ( ( A ) = ( B ) ) ) ))).
% 0.49/0.70  thf('45', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i]:
% 0.49/0.70         ((m1_subset_1 @ (sk_C_2 @ X13 @ X14) @ X14)
% 0.49/0.70          | ((X14) = (X13))
% 0.49/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.70      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      ((((sk_B_2) = (sk_C_3))
% 0.49/0.70        | (m1_subset_1 @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.70  thf('47', plain, (((sk_B_2) != (sk_C_3))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('48', plain, ((m1_subset_1 @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_B_2)),
% 0.49/0.70      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.49/0.70  thf('49', plain,
% 0.49/0.70      (![X17 : $i, X18 : $i]:
% 0.49/0.70         ((r2_hidden @ X17 @ X18)
% 0.49/0.70          | (v1_xboole_0 @ X18)
% 0.49/0.70          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.49/0.70      inference('cnf', [status(esa)], [t2_subset])).
% 0.49/0.70  thf('50', plain,
% 0.49/0.70      (((v1_xboole_0 @ sk_B_2)
% 0.49/0.70        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.70  thf('51', plain,
% 0.49/0.70      (((v1_xboole_0 @ sk_B_2)
% 0.49/0.70        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.70  thf('52', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('53', plain,
% 0.49/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X19 @ X20)
% 0.49/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.49/0.70          | (m1_subset_1 @ X19 @ X21))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset])).
% 0.49/0.70  thf('54', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.70          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.70  thf('55', plain,
% 0.49/0.70      (((v1_xboole_0 @ sk_B_2)
% 0.49/0.70        | (m1_subset_1 @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['51', '54'])).
% 0.49/0.70  thf('56', plain,
% 0.49/0.70      (![X22 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X22 @ sk_B_2)
% 0.49/0.70          | (r2_hidden @ X22 @ sk_C_3)
% 0.49/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('57', plain,
% 0.49/0.70      (((v1_xboole_0 @ sk_B_2)
% 0.49/0.70        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_C_3)
% 0.49/0.70        | ~ (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.70  thf('58', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.70  thf('59', plain,
% 0.49/0.70      ((~ (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_B_2)
% 0.49/0.70        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_C_3))),
% 0.49/0.70      inference('clc', [status(thm)], ['57', '58'])).
% 0.49/0.70  thf('60', plain,
% 0.49/0.70      (((v1_xboole_0 @ sk_B_2)
% 0.49/0.70        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_2) @ sk_C_3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['50', '59'])).
% 0.49/0.70  thf('61', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i]:
% 0.49/0.70         (~ (r2_hidden @ (sk_C_2 @ X13 @ X14) @ X13)
% 0.49/0.70          | ((X14) = (X13))
% 0.49/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.70      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.49/0.70  thf('62', plain,
% 0.49/0.70      (((v1_xboole_0 @ sk_B_2)
% 0.49/0.70        | ~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_2))
% 0.49/0.70        | ((sk_B_2) = (sk_C_3)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.70  thf('63', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.70  thf('64', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_B_2) = (sk_C_3)))),
% 0.49/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.49/0.70  thf('65', plain, (((sk_B_2) != (sk_C_3))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('66', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.49/0.70      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.49/0.70  thf('67', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['28', '66'])).
% 0.49/0.70  thf('68', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['0', '67'])).
% 0.49/0.70  thf('69', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.49/0.70      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.49/0.70  thf('70', plain,
% 0.49/0.70      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.49/0.70  thf('71', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.70  thf('72', plain,
% 0.49/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.49/0.70  thf('73', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['69', '72'])).
% 0.49/0.70  thf('74', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['68', '73'])).
% 0.49/0.70  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
