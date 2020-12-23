%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yfgs0uxhAK

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 448 expanded)
%              Number of leaves         :   21 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  828 (8861 expanded)
%              Number of equality atoms :   60 ( 510 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t155_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_funct_2])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X0 @ X3 @ X5 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ( X1 != X2 )
      | ~ ( v1_partfun1 @ X1 @ X5 )
      | ~ ( r1_partfun1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( r1_partfun1 @ X0 @ X2 )
      | ~ ( v1_partfun1 @ X2 @ X5 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( zip_tseitin_0 @ X2 @ X2 @ X0 @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k5_partfun1 @ X9 @ X8 @ X7 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X13 @ ( k5_partfun1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('30',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['29','35'])).

thf('37',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( r1_partfun1 @ X0 @ X2 )
      | ~ ( v1_partfun1 @ X2 @ X5 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( zip_tseitin_0 @ X2 @ X2 @ X0 @ X3 @ X5 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X17 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ k1_xboole_0 @ X15 )
      | ( v1_partfun1 @ X16 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ~ ( v1_funct_1 @ sk_D )
      | ( v1_partfun1 @ sk_D @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','52'])).

thf('54',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','53'])).

thf('55',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf('56',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('58',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X13 @ ( k5_partfun1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['36','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yfgs0uxhAK
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:31:23 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 99 iterations in 0.065s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(t155_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52           ( ( r1_partfun1 @ C @ D ) =>
% 0.21/0.52             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.52               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52          ( ![D:$i]:
% 0.21/0.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52              ( ( r1_partfun1 @ C @ D ) =>
% 0.21/0.52                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.52                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.21/0.52  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain, (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t132_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.52           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (((X15) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.21/0.52          | (v1_partfun1 @ X16 @ X17)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.21/0.52          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.21/0.52          | ~ (v1_funct_1 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.21/0.52          | (v1_partfun1 @ X16 @ X17)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.21/0.52          | ~ (v1_funct_1 @ X16)
% 0.21/0.52          | ((X15) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52        | (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.52  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, ((((sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d7_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_funct_1 @ C ) ) =>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.21/0.52           ( ![E:$i]:
% 0.21/0.52             ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.52               ( ?[F:$i]:
% 0.21/0.52                 ( ( v1_funct_1 @ F ) & 
% 0.21/0.52                   ( m1_subset_1 @
% 0.21/0.52                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.21/0.52                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, axiom,
% 0.21/0.52    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.21/0.52       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.21/0.52         ( ( F ) = ( E ) ) & 
% 0.21/0.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_funct_1 @ F ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X1 @ X2 @ X0 @ X3 @ X5)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X3)))
% 0.21/0.52          | ((X1) != (X2))
% 0.21/0.52          | ~ (v1_partfun1 @ X1 @ X5)
% 0.21/0.52          | ~ (r1_partfun1 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.52         (~ (r1_partfun1 @ X0 @ X2)
% 0.21/0.52          | ~ (v1_partfun1 @ X2 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X3)))
% 0.21/0.52          | ~ (v1_funct_1 @ X2)
% 0.21/0.52          | (zip_tseitin_0 @ X2 @ X2 @ X0 @ X3 @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.52          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.52  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.21/0.52          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.52          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_B) = (k1_xboole_0))
% 0.21/0.52          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.52          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.21/0.52           ( ![E:$i]:
% 0.21/0.52             ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.52               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (((X11) != (k5_partfun1 @ X9 @ X8 @ X7))
% 0.21/0.52          | (r2_hidden @ X13 @ X11)
% 0.21/0.52          | ~ (zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.21/0.52          | ~ (v1_funct_1 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9)
% 0.21/0.52          | (r2_hidden @ X13 @ (k5_partfun1 @ X9 @ X8 @ X7)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.52  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((((sk_B) = (k1_xboole_0))
% 0.21/0.52        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.52  thf('27', plain, (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '28'])).
% 0.21/0.52  thf('30', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain, ((((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.52  thf('34', plain, ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('35', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['29', '35'])).
% 0.21/0.52  thf('37', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_D @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.52         (~ (r1_partfun1 @ X0 @ X2)
% 0.21/0.52          | ~ (v1_partfun1 @ X2 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X3)))
% 0.21/0.52          | ~ (v1_funct_1 @ X2)
% 0.21/0.52          | (zip_tseitin_0 @ X2 @ X2 @ X0 @ X3 @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ k1_xboole_0)
% 0.21/0.52           | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52           | ~ (v1_partfun1 @ sk_D @ k1_xboole_0)
% 0.21/0.52           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_D @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (((X17) != (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.21/0.52          | (v1_partfun1 @ X16 @ X17)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.21/0.52          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.21/0.52          | ~ (v1_funct_1 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (v1_funct_2 @ X16 @ k1_xboole_0 @ X15)
% 0.21/0.52          | (v1_partfun1 @ X16 @ k1_xboole_0)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X15)))
% 0.21/0.52          | ~ (v1_funct_1 @ X16))),
% 0.21/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((~ (v1_funct_1 @ sk_D)
% 0.21/0.52         | (v1_partfun1 @ sk_D @ k1_xboole_0)
% 0.21/0.52         | ~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.52  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (((v1_partfun1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ k1_xboole_0)
% 0.21/0.52           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '43', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ k1_xboole_0))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '53'])).
% 0.21/0.52  thf('55', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_C @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X14 @ X13 @ X7 @ X8 @ X9)
% 0.21/0.52          | (r2_hidden @ X13 @ (k5_partfun1 @ X9 @ X8 @ X7)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((![X0 : $i, X1 : $i]:
% 0.21/0.52          ((r2_hidden @ X0 @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C))
% 0.21/0.52           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ k1_xboole_0)
% 0.21/0.52           | ~ (v1_funct_1 @ sk_C)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      ((![X0 : $i, X1 : $i]:
% 0.21/0.52          ((r2_hidden @ X0 @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C))
% 0.21/0.52           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ k1_xboole_0)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      ((![X0 : $i, X1 : $i]:
% 0.21/0.52          ((r2_hidden @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.21/0.52           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.52  thf('69', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '70'])).
% 0.21/0.52  thf('72', plain, ($false), inference('demod', [status(thm)], ['36', '71'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
