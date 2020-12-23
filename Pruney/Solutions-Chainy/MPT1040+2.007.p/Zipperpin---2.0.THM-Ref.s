%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6sloaWB0kX

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:17 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 412 expanded)
%              Number of leaves         :   31 ( 136 expanded)
%              Depth                    :   19
%              Number of atoms          : 1046 (4156 expanded)
%              Number of equality atoms :   81 ( 350 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X16 @ X19 @ X21 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( X17 != X18 )
      | ~ ( v1_partfun1 @ X17 @ X21 )
      | ~ ( r1_partfun1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X16: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( r1_partfun1 @ X16 @ X18 )
      | ~ ( v1_partfun1 @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ( zip_tseitin_0 @ X18 @ X18 @ X16 @ X19 @ X21 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B_1 @ sk_A_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X27: $i,X29: $i,X30: $i] :
      ( ( X27
       != ( k5_partfun1 @ X25 @ X24 @ X23 ) )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X29 @ ( k5_partfun1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('48',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('61',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('67',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('70',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('76',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('77',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('89',plain,(
    ! [X16: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( r1_partfun1 @ X16 @ X18 )
      | ~ ( v1_partfun1 @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ( zip_tseitin_0 @ X18 @ X18 @ X16 @ X19 @ X21 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ X1 @ X1 @ X2 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('93',plain,(
    ! [X31: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X31 ) @ X31 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('94',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','96'])).

thf('98',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('99',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','86'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('102',plain,(
    ! [X23: $i,X24: $i,X25: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X29 @ ( k5_partfun1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['65','108'])).

thf('110',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('111',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['35','111'])).

thf('113',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['22','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6sloaWB0kX
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:02:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 630 iterations in 0.287s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.74  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.74  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.53/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.53/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.74  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.53/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.53/0.74  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(t155_funct_2, conjecture,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74           ( ( r1_partfun1 @ C @ D ) =>
% 0.53/0.74             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.53/0.74               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.74        ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74          ( ![D:$i]:
% 0.53/0.74            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.74                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74              ( ( r1_partfun1 @ C @ D ) =>
% 0.53/0.74                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.53/0.74                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(cc5_funct_2, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.53/0.74       ( ![C:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.74           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.53/0.74             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.53/0.74          | (v1_partfun1 @ X13 @ X14)
% 0.53/0.74          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.53/0.74          | ~ (v1_funct_1 @ X13)
% 0.53/0.74          | (v1_xboole_0 @ X15))),
% 0.53/0.74      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (((v1_xboole_0 @ sk_B_1)
% 0.53/0.74        | ~ (v1_funct_1 @ sk_D)
% 0.53/0.74        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1)
% 0.53/0.74        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.74  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.53/0.74      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d7_partfun1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.74         ( v1_funct_1 @ C ) ) =>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.53/0.74           ( ![E:$i]:
% 0.53/0.74             ( ( r2_hidden @ E @ D ) <=>
% 0.53/0.74               ( ?[F:$i]:
% 0.53/0.74                 ( ( v1_funct_1 @ F ) & 
% 0.53/0.74                   ( m1_subset_1 @
% 0.53/0.74                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.74                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.53/0.74                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_1, axiom,
% 0.53/0.74    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.53/0.74     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.53/0.74       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.53/0.74         ( ( F ) = ( E ) ) & 
% 0.53/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.74         ( v1_funct_1 @ F ) ) ))).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ X17 @ X18 @ X16 @ X19 @ X21)
% 0.53/0.74          | ~ (v1_funct_1 @ X17)
% 0.53/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.53/0.74          | ((X17) != (X18))
% 0.53/0.74          | ~ (v1_partfun1 @ X17 @ X21)
% 0.53/0.74          | ~ (r1_partfun1 @ X16 @ X17))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X16 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.53/0.74         (~ (r1_partfun1 @ X16 @ X18)
% 0.53/0.74          | ~ (v1_partfun1 @ X18 @ X21)
% 0.53/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.53/0.74          | ~ (v1_funct_1 @ X18)
% 0.53/0.74          | (zip_tseitin_0 @ X18 @ X18 @ X16 @ X19 @ X21))),
% 0.53/0.74      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1)
% 0.53/0.74          | ~ (v1_funct_1 @ sk_D)
% 0.53/0.74          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.53/0.74          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.53/0.74      inference('sup-', [status(thm)], ['8', '10'])).
% 0.53/0.74  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1)
% 0.53/0.74          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.53/0.74          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.53/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v1_xboole_0 @ sk_B_1)
% 0.53/0.74          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.53/0.74          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['7', '13'])).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B_1 @ sk_A_1)
% 0.53/0.74        | (v1_xboole_0 @ sk_B_1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['1', '14'])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.53/0.74  thf(zf_stmt_3, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.74       ( ![D:$i]:
% 0.53/0.74         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.53/0.74           ( ![E:$i]:
% 0.53/0.74             ( ( r2_hidden @ E @ D ) <=>
% 0.53/0.74               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i, X29 : $i, X30 : $i]:
% 0.53/0.74         (((X27) != (k5_partfun1 @ X25 @ X24 @ X23))
% 0.53/0.74          | (r2_hidden @ X29 @ X27)
% 0.53/0.74          | ~ (zip_tseitin_0 @ X30 @ X29 @ X23 @ X24 @ X25)
% 0.53/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.53/0.74          | ~ (v1_funct_1 @ X23))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i, X29 : $i, X30 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X23)
% 0.53/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.53/0.74          | ~ (zip_tseitin_0 @ X30 @ X29 @ X23 @ X24 @ X25)
% 0.53/0.74          | (r2_hidden @ X29 @ (k5_partfun1 @ X25 @ X24 @ X23)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['17'])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C))
% 0.53/0.74          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A_1)
% 0.53/0.74          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['16', '18'])).
% 0.53/0.74  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C))
% 0.53/0.74          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A_1))),
% 0.53/0.74      inference('demod', [status(thm)], ['19', '20'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (((v1_xboole_0 @ sk_B_1)
% 0.53/0.74        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['15', '21'])).
% 0.53/0.74  thf(l13_xboole_0, axiom,
% 0.53/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.74      inference('sup+', [status(thm)], ['23', '24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      ((((sk_B_1) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['26'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          (((X0) != (k1_xboole_0))
% 0.53/0.74           | ~ (v1_xboole_0 @ X0)
% 0.53/0.74           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.53/0.74         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['25', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.53/0.74         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.53/0.74  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.53/0.74  thf('30', plain, ((v1_xboole_0 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.53/0.74  thf('31', plain, ((v1_xboole_0 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '33'])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('simplify_reflect+', [status(thm)], ['29', '34'])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['26'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_C)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.74  thf(d1_xboole_0, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['26'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (((m1_subset_1 @ sk_C @ 
% 0.53/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['40', '41'])).
% 0.53/0.74  thf(t5_subset, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.53/0.74          ( v1_xboole_0 @ C ) ) ))).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X7 @ X8)
% 0.53/0.74          | ~ (v1_xboole_0 @ X9)
% 0.53/0.74          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t5_subset])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.53/0.74           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.74  thf(t113_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X5 : $i, X6 : $i]:
% 0.53/0.74         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.74  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '33'])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['44', '46', '47'])).
% 0.53/0.74  thf('49', plain, (((v1_xboole_0 @ sk_C)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['39', '48'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      ((~ (r2_hidden @ sk_D @ 
% 0.53/0.74           (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['38', '51'])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('split', [status(esa)], ['26'])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      (((m1_subset_1 @ sk_D @ 
% 0.53/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['54', '55'])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X7 @ X8)
% 0.53/0.74          | ~ (v1_xboole_0 @ X9)
% 0.53/0.74          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t5_subset])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.53/0.74           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.74  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '33'])).
% 0.53/0.74  thf('61', plain,
% 0.53/0.74      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.53/0.74  thf('62', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['53', '61'])).
% 0.53/0.74  thf('63', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('64', plain,
% 0.53/0.74      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.74  thf('65', plain,
% 0.53/0.74      ((~ (r2_hidden @ k1_xboole_0 @ 
% 0.53/0.74           (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['52', '64'])).
% 0.53/0.74  thf('66', plain,
% 0.53/0.74      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.74  thf('67', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('68', plain,
% 0.53/0.74      (((r1_partfun1 @ k1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['66', '67'])).
% 0.53/0.74  thf('69', plain,
% 0.53/0.74      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.74  thf('70', plain,
% 0.53/0.74      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf('71', plain,
% 0.53/0.74      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.74  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('73', plain,
% 0.53/0.74      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['71', '72'])).
% 0.53/0.74  thf('74', plain,
% 0.53/0.74      (![X5 : $i, X6 : $i]:
% 0.53/0.74         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.74  thf('75', plain,
% 0.53/0.74      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['74'])).
% 0.53/0.74  thf(dt_k6_partfun1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( m1_subset_1 @
% 0.53/0.74         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.53/0.74       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.53/0.74  thf('76', plain,
% 0.53/0.74      (![X32 : $i]:
% 0.53/0.74         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.53/0.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.53/0.74  thf('77', plain,
% 0.53/0.74      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['75', '76'])).
% 0.53/0.74  thf('78', plain,
% 0.53/0.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.74  thf('79', plain,
% 0.53/0.74      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['75', '76'])).
% 0.53/0.74  thf('80', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X7 @ X8)
% 0.53/0.74          | ~ (v1_xboole_0 @ X9)
% 0.53/0.74          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t5_subset])).
% 0.53/0.74  thf('81', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.74          | ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.53/0.74  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '33'])).
% 0.53/0.74  thf('83', plain,
% 0.53/0.74      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['81', '82'])).
% 0.53/0.74  thf('84', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['78', '83'])).
% 0.53/0.74  thf('85', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('86', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['84', '85'])).
% 0.53/0.74  thf('87', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['77', '86'])).
% 0.53/0.74  thf('88', plain,
% 0.53/0.74      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.74  thf('89', plain,
% 0.53/0.74      (![X16 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.53/0.74         (~ (r1_partfun1 @ X16 @ X18)
% 0.53/0.74          | ~ (v1_partfun1 @ X18 @ X21)
% 0.53/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.53/0.74          | ~ (v1_funct_1 @ X18)
% 0.53/0.74          | (zip_tseitin_0 @ X18 @ X18 @ X16 @ X19 @ X21))),
% 0.53/0.74      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.74  thf('90', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.53/0.74          | (zip_tseitin_0 @ X1 @ X1 @ X2 @ X0 @ k1_xboole_0)
% 0.53/0.74          | ~ (v1_funct_1 @ X1)
% 0.53/0.74          | ~ (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.53/0.74          | ~ (r1_partfun1 @ X2 @ X1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['88', '89'])).
% 0.53/0.74  thf('91', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.53/0.74          | ~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.53/0.74          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.53/0.74          | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['87', '90'])).
% 0.53/0.74  thf('92', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['84', '85'])).
% 0.53/0.74  thf('93', plain, (![X31 : $i]: (v1_partfun1 @ (k6_partfun1 @ X31) @ X31)),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.53/0.74  thf('94', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('sup+', [status(thm)], ['92', '93'])).
% 0.53/0.74  thf('95', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.53/0.74          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.53/0.74          | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['91', '94'])).
% 0.53/0.74  thf('96', plain,
% 0.53/0.74      ((![X0 : $i, X1 : $i]:
% 0.53/0.74          ((zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 @ k1_xboole_0)
% 0.53/0.74           | ~ (r1_partfun1 @ X1 @ k1_xboole_0)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['73', '95'])).
% 0.53/0.74  thf('97', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ 
% 0.53/0.74           k1_xboole_0))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['70', '96'])).
% 0.53/0.74  thf('98', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('99', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['77', '86'])).
% 0.53/0.74  thf('100', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.53/0.74          | ~ (v1_xboole_0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['98', '99'])).
% 0.53/0.74  thf('101', plain,
% 0.53/0.74      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.74  thf('102', plain,
% 0.53/0.74      (![X23 : $i, X24 : $i, X25 : $i, X29 : $i, X30 : $i]:
% 0.53/0.74         (~ (v1_funct_1 @ X23)
% 0.53/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.53/0.74          | ~ (zip_tseitin_0 @ X30 @ X29 @ X23 @ X24 @ X25)
% 0.53/0.74          | (r2_hidden @ X29 @ (k5_partfun1 @ X25 @ X24 @ X23)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['17'])).
% 0.53/0.74  thf('103', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.53/0.74          | (r2_hidden @ X2 @ (k5_partfun1 @ k1_xboole_0 @ X0 @ X1))
% 0.53/0.74          | ~ (zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 0.53/0.74          | ~ (v1_funct_1 @ X1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['101', '102'])).
% 0.53/0.74  thf('104', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.74         (~ (v1_xboole_0 @ X0)
% 0.53/0.74          | ~ (v1_funct_1 @ X0)
% 0.53/0.74          | ~ (zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 @ k1_xboole_0)
% 0.53/0.74          | (r2_hidden @ X2 @ (k5_partfun1 @ k1_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['100', '103'])).
% 0.53/0.74  thf('105', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          ((r2_hidden @ k1_xboole_0 @ 
% 0.53/0.74            (k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 0.53/0.74           | ~ (v1_funct_1 @ k1_xboole_0)
% 0.53/0.74           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['97', '104'])).
% 0.53/0.74  thf('106', plain,
% 0.53/0.74      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['71', '72'])).
% 0.53/0.74  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '33'])).
% 0.53/0.74  thf('108', plain,
% 0.53/0.74      ((![X0 : $i]:
% 0.53/0.74          (r2_hidden @ k1_xboole_0 @ 
% 0.53/0.74           (k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))
% 0.53/0.74         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.53/0.74  thf('109', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['65', '108'])).
% 0.53/0.74  thf('110', plain,
% 0.53/0.74      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.53/0.74      inference('split', [status(esa)], ['26'])).
% 0.53/0.74  thf('111', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.53/0.74      inference('sat_resolution*', [status(thm)], ['109', '110'])).
% 0.53/0.74  thf('112', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.53/0.74      inference('simpl_trail', [status(thm)], ['35', '111'])).
% 0.53/0.74  thf('113', plain,
% 0.53/0.74      ((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C))),
% 0.53/0.74      inference('clc', [status(thm)], ['22', '112'])).
% 0.53/0.74  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
