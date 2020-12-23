%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.acvSmKUHgu

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 554 expanded)
%              Number of leaves         :   35 ( 183 expanded)
%              Depth                    :   23
%              Number of atoms          : 1384 (9112 expanded)
%              Number of equality atoms :  204 (1391 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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

thf('0',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X49
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k6_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k7_mcart_1 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X46 @ X47 @ X48 ) )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X49
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k6_mcart_1 @ X46 @ X47 @ X48 @ X49 ) @ ( k7_mcart_1 @ X46 @ X47 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ X48 ) )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('14',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k3_zfmisc_1 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k3_zfmisc_1 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('32',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k3_zfmisc_1 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('33',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_zfmisc_1 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','21','30','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('46',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38'])).

thf('50',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('51',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('53',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k3_mcart_1 @ X33 @ X34 @ X35 )
      = ( k4_tarski @ ( k4_tarski @ X33 @ X34 ) @ X35 ) ) ),
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

thf('55',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39
       != ( k2_mcart_1 @ X39 ) )
      | ( X39
       != ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('56',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_tarski @ X40 @ X41 )
     != ( k2_mcart_1 @ ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('57',plain,(
    ! [X54: $i,X56: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X54 @ X56 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('58',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k4_tarski @ X40 @ X41 )
     != X41 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('62',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('63',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('64',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('66',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r2_hidden @ X43 @ X42 )
      | ( ( sk_B @ X42 )
       != ( k3_mcart_1 @ X44 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('71',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('72',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('75',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X30 )
       != ( k2_tarski @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('86',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('87',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X30 )
       != ( k2_tarski @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['88','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['71','96'])).

thf('98',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('100',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['60','98','99'])).

thf('101',plain,
    ( sk_D_1
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['48','100'])).

thf('102',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','101'])).

thf('103',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r2_hidden @ X44 @ X42 )
      | ( ( sk_B @ X42 )
       != ( k3_mcart_1 @ X44 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('107',plain,(
    ( sk_B @ ( k1_tarski @ sk_D_1 ) )
 != sk_D_1 ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_D_1 != sk_D_1 )
    | ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','107'])).

thf('109',plain,
    ( ( k1_tarski @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('111',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference(simplify,[status(thm)],['111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.acvSmKUHgu
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 155 iterations in 0.069s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.52  thf(t29_mcart_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.52                 ( ![C:$i,D:$i,E:$i]:
% 0.20/0.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.52                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X42 : $i]:
% 0.20/0.52         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.52  thf(d1_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X24 @ X23)
% 0.20/0.52          | ((X24) = (X21))
% 0.20/0.52          | ((X23) != (k1_tarski @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X21 : $i, X24 : $i]:
% 0.20/0.52         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.52         (((X22) != (X21))
% 0.20/0.52          | (r2_hidden @ X22 @ X23)
% 0.20/0.52          | ((X23) != (k1_tarski @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.52  thf('5', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.20/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.52  thf(t51_mcart_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ~( ![D:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.52                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.52                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.52                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52             ( ~( ![D:$i]:
% 0.20/0.52                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.52                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.52                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.52                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.52       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.52        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf(t48_mcart_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ~( ![D:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.52                 ( ( D ) =
% 0.20/0.52                   ( k3_mcart_1 @
% 0.20/0.52                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.52                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.52                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.52         (((X46) = (k1_xboole_0))
% 0.20/0.52          | ((X47) = (k1_xboole_0))
% 0.20/0.53          | ((X49)
% 0.20/0.53              = (k3_mcart_1 @ (k5_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.20/0.53                 (k6_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.20/0.53                 (k7_mcart_1 @ X46 @ X47 @ X48 @ X49)))
% 0.20/0.53          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X46 @ X47 @ X48))
% 0.20/0.53          | ((X48) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.53         (((X46) = (k1_xboole_0))
% 0.20/0.53          | ((X47) = (k1_xboole_0))
% 0.20/0.53          | ((X49)
% 0.20/0.53              = (k3_mcart_1 @ (k5_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.20/0.53                 (k6_mcart_1 @ X46 @ X47 @ X48 @ X49) @ 
% 0.20/0.53                 (k7_mcart_1 @ X46 @ X47 @ X48 @ X49)))
% 0.20/0.53          | ~ (m1_subset_1 @ X49 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47) @ X48))
% 0.20/0.53          | ((X48) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_1)
% 0.20/0.53            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.53               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.53               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
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
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k5_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.20/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ (k3_zfmisc_1 @ X50 @ X51 @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k5_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.20/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.53  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('20', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k6_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ (k3_zfmisc_1 @ X50 @ X51 @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k6_mcart_1 @ X50 @ X51 @ X53 @ X52)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.53  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('29', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k7_mcart_1 @ X50 @ X51 @ X53 @ X52) = (k2_mcart_1 @ X52))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ (k3_zfmisc_1 @ X50 @ X51 @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X36 @ X37 @ X38)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37) @ X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k7_mcart_1 @ X50 @ X51 @ X53 @ X52) = (k2_mcart_1 @ X52))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ 
% 0.20/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53            = (k2_mcart_1 @ sk_D_1))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.53  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36', '37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_1)
% 0.20/0.53            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '21', '30', '39'])).
% 0.20/0.53  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((sk_D_1)
% 0.20/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))
% 0.20/0.53        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))
% 0.20/0.53        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.20/0.53         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.20/0.53         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['45', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36', '37', '38'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.20/0.53         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.20/0.53         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (((sk_D_1)
% 0.20/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((((sk_D_1)
% 0.20/0.53          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.53             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.20/0.53         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf(d3_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ X33 @ X34 @ X35)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X33 @ X34) @ X35))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.53  thf(t20_mcart_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.53         (((X39) != (k2_mcart_1 @ X39)) | ((X39) != (k4_tarski @ X40 @ X41)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X40 : $i, X41 : $i]:
% 0.20/0.53         ((k4_tarski @ X40 @ X41) != (k2_mcart_1 @ (k4_tarski @ X40 @ X41)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.53  thf(t7_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X54 : $i, X56 : $i]: ((k2_mcart_1 @ (k4_tarski @ X54 @ X56)) = (X56))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.53  thf('58', plain, (![X40 : $i, X41 : $i]: ((k4_tarski @ X40 @ X41) != (X41))),
% 0.20/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['53', '59'])).
% 0.20/0.53  thf('61', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.20/0.53         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.20/0.53         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (((sk_D_1)
% 0.20/0.53         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.53         (((X42) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X43 @ X42)
% 0.20/0.53          | ((sk_B @ X42) != (k3_mcart_1 @ X44 @ X43 @ X45)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B @ X0) != (sk_D_1))
% 0.20/0.53          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ X0)
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.20/0.53           | ((X0) = (k1_xboole_0))
% 0.20/0.53           | ((sk_B @ X0) != (sk_D_1))))
% 0.20/0.53         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.20/0.53         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.20/0.53         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['61', '68'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.20/0.53         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('72', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf(t48_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.53           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(t72_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.53       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X29 @ X30)
% 0.20/0.53          | ((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X30)
% 0.20/0.53              != (k2_tarski @ X29 @ X31)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['74', '79'])).
% 0.20/0.53  thf('81', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.20/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X42 : $i]:
% 0.20/0.53         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf(d4_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.53          | (r2_hidden @ X4 @ X2)
% 0.20/0.53          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.53         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.20/0.53          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '87'])).
% 0.20/0.53  thf('89', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X29 @ X30)
% 0.20/0.53          | ((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X30)
% 0.20/0.53              != (k2_tarski @ X29 @ X31)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.53  thf('92', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['88', '92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '93'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['83', '94'])).
% 0.20/0.53  thf('96', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '95'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.53         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['71', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (~ (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))) | 
% 0.20/0.53       (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))) | 
% 0.20/0.53       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['46'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['60', '98', '99'])).
% 0.20/0.53  thf('101', plain, (((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['48', '100'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (((sk_D_1)
% 0.20/0.53         = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.53            (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '101'])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.53         (((X42) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X44 @ X42)
% 0.20/0.53          | ((sk_B @ X42) != (k3_mcart_1 @ X44 @ X43 @ X45)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_B @ X0) != (sk_D_1))
% 0.20/0.53          | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      ((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '104'])).
% 0.20/0.53  thf('106', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '95'])).
% 0.20/0.53  thf('107', plain, (((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      ((((sk_D_1) != (sk_D_1)) | ((k1_tarski @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '107'])).
% 0.20/0.53  thf('109', plain, (((k1_tarski @ sk_D_1) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['108'])).
% 0.20/0.53  thf('110', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '95'])).
% 0.20/0.53  thf('111', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.53  thf('112', plain, ($false), inference('simplify', [status(thm)], ['111'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
