%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YZtMk0NmqJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 (1201 expanded)
%              Number of leaves         :   35 ( 380 expanded)
%              Depth                    :   23
%              Number of atoms          : 1412 (22413 expanded)
%              Number of equality atoms :  213 (3518 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_2 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('12',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X44 @ X45 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X44 @ X45 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X44 @ X45 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('32',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
      = ( k2_mcart_1 @ sk_D_2 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
    = ( k2_mcart_1 @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','19','28','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('44',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_D_2
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
    = ( k2_mcart_1 @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34','35','36'])).

thf('48',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('49',plain,
    ( ( sk_D_2
      = ( k2_mcart_1 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41'])).

thf('51',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k2_mcart_1 @ X33 ) )
      | ( X33
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('54',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != ( k2_mcart_1 @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('55',plain,(
    ! [X48: $i,X50: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X48 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X35 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('60',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('61',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('62',plain,
    ( ( sk_D_2
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('64',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('69',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,(
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ( X14 = X13 )
      | ( X14 = X10 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('71',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,
    ( ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['67','74'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('76',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('80',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('81',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X24 )
       != ( k2_tarski @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k1_tarski @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('89',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['67','74'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['87','90','91'])).

thf('93',plain,(
    sk_D_2
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('95',plain,
    ( sk_D_2
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['58','93','94'])).

thf('96',plain,
    ( sk_D_2
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['46','95'])).

thf('97',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ sk_D_2 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['42','96'])).

thf('98',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ sk_D_2 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_D_2 ) )
     != sk_D_2 ) ),
    inference('sup-',[status(thm)],['3','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('102',plain,
    ( ( k1_tarski @ sk_D_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != ( k2_tarski @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('110',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('111',plain,
    ( ( k1_tarski @ sk_D_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['100','101'])).

thf('112',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    $false ),
    inference(simplify,[status(thm)],['112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YZtMk0NmqJ
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 154 iterations in 0.077s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('0', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(d2_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (((X11) != (X10))
% 0.20/0.53          | (r2_hidden @ X11 @ X12)
% 0.20/0.53          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 0.20/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.53  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.53  thf(t51_mcart_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![D:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.53                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.53                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53             ( ~( ![D:$i]:
% 0.20/0.53                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.53                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.53                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(t48_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![D:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                 ( ( D ) =
% 0.20/0.53                   ( k3_mcart_1 @
% 0.20/0.53                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.53                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.53                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.53         (((X40) = (k1_xboole_0))
% 0.20/0.53          | ((X41) = (k1_xboole_0))
% 0.20/0.53          | ((X43)
% 0.20/0.53              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.20/0.53                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.20/0.53                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.20/0.53          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X40 @ X41 @ X42))
% 0.20/0.53          | ((X42) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.53         (((X40) = (k1_xboole_0))
% 0.20/0.53          | ((X41) = (k1_xboole_0))
% 0.20/0.53          | ((X43)
% 0.20/0.53              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.20/0.53                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.20/0.53                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.20/0.53          | ~ (m1_subset_1 @ X43 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))
% 0.20/0.53          | ((X42) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((((sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_2)
% 0.20/0.53            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.20/0.53               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.20/0.53               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(t50_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![D:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.53                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.53                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((k5_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.20/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.20/0.53          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X44 @ X45 @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((k5_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.20/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.20/0.53          | ~ (m1_subset_1 @ X46 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)
% 0.20/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.53  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)
% 0.20/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((k6_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.20/0.53          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X44 @ X45 @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((k6_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.20/0.53          | ~ (m1_subset_1 @ X46 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)
% 0.20/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.53  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)
% 0.20/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((k7_mcart_1 @ X44 @ X45 @ X47 @ X46) = (k2_mcart_1 @ X46))
% 0.20/0.53          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X44 @ X45 @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((k7_mcart_1 @ X44 @ X45 @ X47 @ X46) = (k2_mcart_1 @ X46))
% 0.20/0.53          | ~ (m1_subset_1 @ X46 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) = (k2_mcart_1 @ sk_D_2))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.53  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) = (k2_mcart_1 @ sk_D_2))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_2)
% 0.20/0.53            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 0.20/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '19', '28', '37'])).
% 0.20/0.53  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((sk_D_2)
% 0.20/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)
% 0.20/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 0.20/0.53        | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 0.20/0.53        | ((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.20/0.53         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((sk_D_2) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2))))
% 0.20/0.53         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['43', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) = (k2_mcart_1 @ sk_D_2))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.20/0.53         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((((sk_D_2) = (k2_mcart_1 @ sk_D_2)))
% 0.20/0.53         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((sk_D_2)
% 0.20/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((((sk_D_2)
% 0.20/0.53          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 0.20/0.53             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ sk_D_2)))
% 0.20/0.53         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf(d3_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.53  thf(t20_mcart_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.53         (((X33) != (k2_mcart_1 @ X33)) | ((X33) != (k4_tarski @ X34 @ X35)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X34 : $i, X35 : $i]:
% 0.20/0.53         ((k4_tarski @ X34 @ X35) != (k2_mcart_1 @ (k4_tarski @ X34 @ X35)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.53  thf(t7_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X48 : $i, X50 : $i]: ((k2_mcart_1 @ (k4_tarski @ X48 @ X50)) = (X50))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.53  thf('56', plain, (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X35))),
% 0.20/0.53      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (~ (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['51', '57'])).
% 0.20/0.53  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)
% 0.20/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((((sk_D_2) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2))))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((sk_D_2)
% 0.20/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.53  thf(t29_mcart_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.53                 ( ![C:$i,D:$i,E:$i]:
% 0.20/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.53                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.53         (((X36) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X37 @ X36)
% 0.20/0.53          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B @ X0) != (sk_D_2))
% 0.20/0.53          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ X0)
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.20/0.53           | ((X0) = (k1_xboole_0))
% 0.20/0.53           | ((sk_B @ X0) != (sk_D_2))))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((((sk_B @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.20/0.53         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X36 : $i]:
% 0.20/0.53         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X14 @ X12)
% 0.20/0.53          | ((X14) = (X13))
% 0.20/0.53          | ((X14) = (X10))
% 0.20/0.53          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X10 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (((X14) = (X10))
% 0.20/0.53          | ((X14) = (X13))
% 0.20/0.53          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      ((((k1_tarski @ sk_D_2) = (k1_xboole_0)))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('clc', [status(thm)], ['67', '74'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('76', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf(t48_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.53           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(t72_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.53       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X23 @ X24)
% 0.20/0.53          | ((k4_xboole_0 @ (k2_tarski @ X23 @ X25) @ X24)
% 0.20/0.53              != (k2_tarski @ X23 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['79', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['78', '83'])).
% 0.20/0.53  thf('85', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_tarski @ sk_D_2)))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['75', '86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.53           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf(t4_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      ((((k1_tarski @ sk_D_2) = (k1_xboole_0)))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('clc', [status(thm)], ['67', '74'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.20/0.53      inference('demod', [status(thm)], ['87', '90', '91'])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (~ (((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 0.20/0.53       (((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 0.20/0.53       (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['58', '93', '94'])).
% 0.20/0.53  thf('96', plain, (((sk_D_2) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['46', '95'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      (((sk_D_2)
% 0.20/0.53         = (k3_mcart_1 @ sk_D_2 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 0.20/0.53            (k2_mcart_1 @ sk_D_2)))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.53         (((X36) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X38 @ X36)
% 0.20/0.53          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B @ X0) != (sk_D_2))
% 0.20/0.53          | ~ (r2_hidden @ sk_D_2 @ X0)
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B @ (k1_tarski @ sk_D_2)) != (sk_D_2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '99'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '73'])).
% 0.20/0.53  thf('102', plain, (((k1_tarski @ sk_D_2) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.20/0.53            != (k2_tarski @ X0 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.20/0.53           != (k2_tarski @ X0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.53         != (k2_tarski @ sk_D_2 @ sk_D_2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['102', '107'])).
% 0.20/0.53  thf('109', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('111', plain, (((k1_tarski @ sk_D_2) = (k1_xboole_0))),
% 0.20/0.53      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.53  thf('112', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.20/0.53  thf('113', plain, ($false), inference('simplify', [status(thm)], ['112'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
