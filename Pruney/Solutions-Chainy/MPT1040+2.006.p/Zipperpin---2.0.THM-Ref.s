%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cMRWF6ipXu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:16 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 390 expanded)
%              Number of leaves         :   29 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          : 1010 (4012 expanded)
%              Number of equality atoms :   81 ( 350 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf('0',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( v1_partfun1 @ X6 @ X7 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X9 @ X12 @ X14 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( X10 != X11 )
      | ~ ( v1_partfun1 @ X10 @ X14 )
      | ~ ( r1_partfun1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X9: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( r1_partfun1 @ X9 @ X11 )
      | ~ ( v1_partfun1 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( zip_tseitin_0 @ X11 @ X11 @ X9 @ X12 @ X14 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A_1 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i,X22: $i,X23: $i] :
      ( ( X20
       != ( k5_partfun1 @ X18 @ X17 @ X16 ) )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( zip_tseitin_0 @ X23 @ X22 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( zip_tseitin_0 @ X23 @ X22 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X22 @ ( k5_partfun1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A_1 @ sk_B @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A_1 @ sk_B @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('30',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('31',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','43'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','50'])).

thf('52',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('58',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('65',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('68',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('74',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('75',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('80',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('85',plain,(
    ! [X9: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( r1_partfun1 @ X9 @ X11 )
      | ~ ( v1_partfun1 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( zip_tseitin_0 @ X11 @ X11 @ X9 @ X12 @ X14 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ X1 @ X1 @ X2 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('89',plain,(
    ! [X24: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('90',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( zip_tseitin_0 @ X23 @ X22 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X22 @ ( k5_partfun1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','104'])).

thf('106',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['35','107'])).

thf('109',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['22','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cMRWF6ipXu
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:54:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 557 iterations in 0.254s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.72  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.52/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.72  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.52/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.72  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.72  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.52/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.52/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.72  thf(t155_funct_2, conjecture,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.72       ( ![D:$i]:
% 0.52/0.72         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.72           ( ( r1_partfun1 @ C @ D ) =>
% 0.52/0.72             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.52/0.72               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.72        ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.72          ( ![D:$i]:
% 0.52/0.72            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.72              ( ( r1_partfun1 @ C @ D ) =>
% 0.52/0.72                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.52/0.72                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B @ sk_C))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('1', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(cc5_funct_2, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.72       ( ![C:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.72           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.52/0.72             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.52/0.72          | (v1_partfun1 @ X6 @ X7)
% 0.52/0.72          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 0.52/0.72          | ~ (v1_funct_1 @ X6)
% 0.52/0.72          | (v1_xboole_0 @ X8))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (((v1_xboole_0 @ sk_B)
% 0.52/0.72        | ~ (v1_funct_1 @ sk_D)
% 0.52/0.72        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)
% 0.52/0.72        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.52/0.72      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(d7_partfun1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.72         ( v1_funct_1 @ C ) ) =>
% 0.52/0.72       ( ![D:$i]:
% 0.52/0.72         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.52/0.72           ( ![E:$i]:
% 0.52/0.72             ( ( r2_hidden @ E @ D ) <=>
% 0.52/0.72               ( ?[F:$i]:
% 0.52/0.72                 ( ( v1_funct_1 @ F ) & 
% 0.52/0.72                   ( m1_subset_1 @
% 0.52/0.72                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.72                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.52/0.72                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_1, axiom,
% 0.52/0.72    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.52/0.72     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.52/0.72       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.52/0.72         ( ( F ) = ( E ) ) & 
% 0.52/0.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.72         ( v1_funct_1 @ F ) ) ))).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ X10 @ X11 @ X9 @ X12 @ X14)
% 0.52/0.72          | ~ (v1_funct_1 @ X10)
% 0.52/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.52/0.72          | ((X10) != (X11))
% 0.52/0.72          | ~ (v1_partfun1 @ X10 @ X14)
% 0.52/0.72          | ~ (r1_partfun1 @ X9 @ X10))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (![X9 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.72         (~ (r1_partfun1 @ X9 @ X11)
% 0.52/0.72          | ~ (v1_partfun1 @ X11 @ X14)
% 0.52/0.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.52/0.72          | ~ (v1_funct_1 @ X11)
% 0.52/0.72          | (zip_tseitin_0 @ X11 @ X11 @ X9 @ X12 @ X14))),
% 0.52/0.72      inference('simplify', [status(thm)], ['9'])).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A_1)
% 0.52/0.72          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.72          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.52/0.72          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.52/0.72      inference('sup-', [status(thm)], ['8', '10'])).
% 0.52/0.72  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A_1)
% 0.52/0.72          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.52/0.72          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((v1_xboole_0 @ sk_B)
% 0.52/0.72          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.52/0.72          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A_1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['7', '13'])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B @ sk_A_1)
% 0.52/0.72        | (v1_xboole_0 @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['1', '14'])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.52/0.72  thf(zf_stmt_3, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.72       ( ![D:$i]:
% 0.52/0.72         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.52/0.72           ( ![E:$i]:
% 0.52/0.72             ( ( r2_hidden @ E @ D ) <=>
% 0.52/0.72               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 0.52/0.72         (((X20) != (k5_partfun1 @ X18 @ X17 @ X16))
% 0.52/0.72          | (r2_hidden @ X22 @ X20)
% 0.52/0.72          | ~ (zip_tseitin_0 @ X23 @ X22 @ X16 @ X17 @ X18)
% 0.52/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.52/0.72          | ~ (v1_funct_1 @ X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X16 : $i, X17 : $i, X18 : $i, X22 : $i, X23 : $i]:
% 0.52/0.72         (~ (v1_funct_1 @ X16)
% 0.52/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X23 @ X22 @ X16 @ X17 @ X18)
% 0.52/0.72          | (r2_hidden @ X22 @ (k5_partfun1 @ X18 @ X17 @ X16)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A_1 @ sk_B @ sk_C))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A_1)
% 0.52/0.72          | ~ (v1_funct_1 @ sk_C))),
% 0.52/0.72      inference('sup-', [status(thm)], ['16', '18'])).
% 0.52/0.72  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A_1 @ sk_B @ sk_C))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ sk_A_1))),
% 0.52/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (((v1_xboole_0 @ sk_B)
% 0.52/0.72        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B @ sk_C)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['15', '21'])).
% 0.52/0.72  thf(l13_xboole_0, axiom,
% 0.52/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['23', '24'])).
% 0.52/0.72  thf('26', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['26'])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          (((X0) != (k1_xboole_0))
% 0.52/0.72           | ~ (v1_xboole_0 @ X0)
% 0.52/0.72           | ~ (v1_xboole_0 @ sk_B)))
% 0.52/0.72         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['25', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.52/0.72         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.52/0.72      inference('simplify', [status(thm)], ['28'])).
% 0.52/0.72  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.52/0.72  thf('30', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.52/0.72  thf('31', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.52/0.72  thf('32', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.72  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['30', '33'])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.52/0.72      inference('simplify_reflect+', [status(thm)], ['29', '34'])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['26'])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B @ sk_C))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['26'])).
% 0.52/0.72  thf('40', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (((m1_subset_1 @ sk_C @ 
% 0.52/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.72  thf(t113_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]:
% 0.52/0.72         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.72  thf('44', plain,
% 0.52/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['41', '43'])).
% 0.52/0.72  thf(cc1_subset_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_xboole_0 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      (![X4 : $i, X5 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.52/0.72          | (v1_xboole_0 @ X4)
% 0.52/0.72          | ~ (v1_xboole_0 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.72  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['30', '33'])).
% 0.52/0.72  thf('48', plain, (((v1_xboole_0 @ sk_C)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['46', '47'])).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('50', plain,
% 0.52/0.72      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.72  thf('51', plain,
% 0.52/0.72      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['38', '50'])).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['26'])).
% 0.52/0.72  thf('53', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('54', plain,
% 0.52/0.72      (((m1_subset_1 @ sk_D @ 
% 0.52/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['52', '53'])).
% 0.52/0.72  thf('55', plain,
% 0.52/0.72      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.72  thf('56', plain,
% 0.52/0.72      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.52/0.72  thf('57', plain,
% 0.52/0.72      (![X4 : $i, X5 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.52/0.72          | (v1_xboole_0 @ X4)
% 0.52/0.72          | ~ (v1_xboole_0 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.52/0.72  thf('58', plain,
% 0.52/0.72      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.72  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['30', '33'])).
% 0.52/0.72  thf('60', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['58', '59'])).
% 0.52/0.72  thf('61', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('62', plain,
% 0.52/0.72      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['60', '61'])).
% 0.52/0.72  thf('63', plain,
% 0.52/0.72      ((~ (r2_hidden @ k1_xboole_0 @ 
% 0.52/0.72           (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['51', '62'])).
% 0.52/0.72  thf('64', plain,
% 0.52/0.72      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.72  thf('65', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('66', plain,
% 0.52/0.72      (((r1_partfun1 @ k1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['64', '65'])).
% 0.52/0.72  thf('67', plain,
% 0.52/0.72      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['60', '61'])).
% 0.52/0.72  thf('68', plain,
% 0.52/0.72      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['66', '67'])).
% 0.52/0.72  thf('69', plain,
% 0.52/0.72      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.72  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('71', plain,
% 0.52/0.72      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['69', '70'])).
% 0.52/0.72  thf('72', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]:
% 0.52/0.72         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.72  thf('73', plain,
% 0.52/0.72      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['72'])).
% 0.52/0.72  thf(dt_k6_partfun1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( m1_subset_1 @
% 0.52/0.72         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.52/0.72       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.52/0.72  thf('74', plain,
% 0.52/0.72      (![X25 : $i]:
% 0.52/0.72         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.52/0.72  thf('75', plain,
% 0.52/0.72      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['73', '74'])).
% 0.52/0.72  thf('76', plain,
% 0.52/0.72      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['73', '74'])).
% 0.52/0.72  thf('77', plain,
% 0.52/0.72      (![X4 : $i, X5 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.52/0.72          | (v1_xboole_0 @ X4)
% 0.52/0.72          | ~ (v1_xboole_0 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.52/0.72  thf('78', plain,
% 0.52/0.72      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.72        | (v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['76', '77'])).
% 0.52/0.72  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['30', '33'])).
% 0.52/0.72  thf('80', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['78', '79'])).
% 0.52/0.72  thf('81', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('82', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.52/0.72  thf('83', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['75', '82'])).
% 0.52/0.72  thf('84', plain,
% 0.52/0.72      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.72  thf('85', plain,
% 0.52/0.72      (![X9 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.72         (~ (r1_partfun1 @ X9 @ X11)
% 0.52/0.72          | ~ (v1_partfun1 @ X11 @ X14)
% 0.52/0.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.52/0.72          | ~ (v1_funct_1 @ X11)
% 0.52/0.72          | (zip_tseitin_0 @ X11 @ X11 @ X9 @ X12 @ X14))),
% 0.52/0.72      inference('simplify', [status(thm)], ['9'])).
% 0.52/0.72  thf('86', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.72          | (zip_tseitin_0 @ X1 @ X1 @ X2 @ X0 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_funct_1 @ X1)
% 0.52/0.72          | ~ (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.52/0.72          | ~ (r1_partfun1 @ X2 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['84', '85'])).
% 0.52/0.72  thf('87', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.52/0.72          | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['83', '86'])).
% 0.52/0.72  thf('88', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.52/0.72  thf('89', plain, (![X24 : $i]: (v1_partfun1 @ (k6_partfun1 @ X24) @ X24)),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.52/0.72  thf('90', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('sup+', [status(thm)], ['88', '89'])).
% 0.52/0.72  thf('91', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.52/0.72          | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['87', '90'])).
% 0.52/0.72  thf('92', plain,
% 0.52/0.72      ((![X0 : $i, X1 : $i]:
% 0.52/0.72          ((zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 @ k1_xboole_0)
% 0.52/0.72           | ~ (r1_partfun1 @ X1 @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['71', '91'])).
% 0.52/0.72  thf('93', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ 
% 0.52/0.72           k1_xboole_0))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['68', '92'])).
% 0.52/0.72  thf('94', plain,
% 0.52/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.72  thf('95', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['75', '82'])).
% 0.52/0.72  thf('96', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.72          | ~ (v1_xboole_0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['94', '95'])).
% 0.52/0.72  thf('97', plain,
% 0.52/0.72      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.72  thf('98', plain,
% 0.52/0.72      (![X16 : $i, X17 : $i, X18 : $i, X22 : $i, X23 : $i]:
% 0.52/0.72         (~ (v1_funct_1 @ X16)
% 0.52/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X23 @ X22 @ X16 @ X17 @ X18)
% 0.52/0.72          | (r2_hidden @ X22 @ (k5_partfun1 @ X18 @ X17 @ X16)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.72  thf('99', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.72          | (r2_hidden @ X2 @ (k5_partfun1 @ k1_xboole_0 @ X0 @ X1))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_funct_1 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['97', '98'])).
% 0.52/0.72  thf('100', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.72         (~ (v1_xboole_0 @ X0)
% 0.52/0.72          | ~ (v1_funct_1 @ X0)
% 0.52/0.72          | ~ (zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 @ k1_xboole_0)
% 0.52/0.72          | (r2_hidden @ X2 @ (k5_partfun1 @ k1_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['96', '99'])).
% 0.52/0.72  thf('101', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          ((r2_hidden @ k1_xboole_0 @ 
% 0.52/0.72            (k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 0.52/0.72           | ~ (v1_funct_1 @ k1_xboole_0)
% 0.52/0.72           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['93', '100'])).
% 0.52/0.72  thf('102', plain,
% 0.52/0.72      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['69', '70'])).
% 0.52/0.72  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['30', '33'])).
% 0.52/0.72  thf('104', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          (r2_hidden @ k1_xboole_0 @ 
% 0.52/0.72           (k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))
% 0.52/0.72         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.52/0.72  thf('105', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['63', '104'])).
% 0.52/0.72  thf('106', plain,
% 0.52/0.72      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.52/0.72      inference('split', [status(esa)], ['26'])).
% 0.52/0.72  thf('107', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 0.52/0.72  thf('108', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.72      inference('simpl_trail', [status(thm)], ['35', '107'])).
% 0.52/0.72  thf('109', plain,
% 0.52/0.72      ((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B @ sk_C))),
% 0.52/0.72      inference('clc', [status(thm)], ['22', '108'])).
% 0.52/0.72  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
