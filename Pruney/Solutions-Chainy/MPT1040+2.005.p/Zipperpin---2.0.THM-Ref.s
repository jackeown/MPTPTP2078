%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uDiB6Tr6by

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:16 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 471 expanded)
%              Number of leaves         :   30 ( 148 expanded)
%              Depth                    :   19
%              Number of atoms          : 1018 (5544 expanded)
%              Number of equality atoms :   95 ( 496 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

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
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X18 @ X21 @ X23 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( X19 != X20 )
      | ~ ( v1_partfun1 @ X19 @ X23 )
      | ~ ( r1_partfun1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X18: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( r1_partfun1 @ X18 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( zip_tseitin_0 @ X20 @ X20 @ X18 @ X21 @ X23 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X29: $i,X31: $i,X32: $i] :
      ( ( X29
       != ( k5_partfun1 @ X27 @ X26 @ X25 ) )
      | ( r2_hidden @ X31 @ X29 )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X31 @ ( k5_partfun1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
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
    | ( sk_A = k1_xboole_0 ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('44',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

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
    inference('sup-',[status(thm)],['30','34'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','46','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('56',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','34'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('66',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('69',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( r1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X18: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( r1_partfun1 @ X18 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( zip_tseitin_0 @ X20 @ X20 @ X18 @ X21 @ X23 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_B_1 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A )
        | ~ ( r1_partfun1 @ X0 @ sk_C )
        | ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_B_1 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('79',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('80',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('81',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','34'])).

thf('85',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('87',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X33 ) @ X33 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('89',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('91',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('92',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','89','90','91','92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','94'])).

thf('96',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_B_1 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('98',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','34'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','34'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('104',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('105',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103','104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','105'])).

thf('107',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('108',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['36','108'])).

thf('110',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['22','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uDiB6Tr6by
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 577 iterations in 0.325s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.78  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.58/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.58/0.78  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.58/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.58/0.78  thf(t155_funct_2, conjecture,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78       ( ![D:$i]:
% 0.58/0.78         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78           ( ( r1_partfun1 @ C @ D ) =>
% 0.58/0.78             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.58/0.78               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.78        ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.78            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78          ( ![D:$i]:
% 0.58/0.78            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.78                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78              ( ( r1_partfun1 @ C @ D ) =>
% 0.58/0.78                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.58/0.78                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.58/0.78  thf('0', plain,
% 0.58/0.78      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('1', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(cc5_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.58/0.78       ( ![C:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.58/0.78             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.58/0.78          | (v1_partfun1 @ X15 @ X16)
% 0.58/0.78          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.58/0.78          | ~ (v1_funct_1 @ X15)
% 0.58/0.78          | (v1_xboole_0 @ X17))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.58/0.78  thf('4', plain,
% 0.58/0.78      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_D)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.58/0.78        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.78  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.58/0.78  thf('8', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(d7_partfun1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.78         ( v1_funct_1 @ C ) ) =>
% 0.58/0.78       ( ![D:$i]:
% 0.58/0.78         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.58/0.78           ( ![E:$i]:
% 0.58/0.78             ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.78               ( ?[F:$i]:
% 0.58/0.78                 ( ( v1_funct_1 @ F ) & 
% 0.58/0.78                   ( m1_subset_1 @
% 0.58/0.78                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.78                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.58/0.78                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_1, axiom,
% 0.58/0.78    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.78     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.58/0.78       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.58/0.78         ( ( F ) = ( E ) ) & 
% 0.58/0.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.78         ( v1_funct_1 @ F ) ) ))).
% 0.58/0.78  thf('9', plain,
% 0.58/0.78      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.58/0.78         ((zip_tseitin_0 @ X19 @ X20 @ X18 @ X21 @ X23)
% 0.58/0.78          | ~ (v1_funct_1 @ X19)
% 0.58/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.58/0.78          | ((X19) != (X20))
% 0.58/0.78          | ~ (v1_partfun1 @ X19 @ X23)
% 0.58/0.78          | ~ (r1_partfun1 @ X18 @ X19))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.78  thf('10', plain,
% 0.58/0.78      (![X18 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.58/0.78         (~ (r1_partfun1 @ X18 @ X20)
% 0.58/0.78          | ~ (v1_partfun1 @ X20 @ X23)
% 0.58/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.58/0.78          | ~ (v1_funct_1 @ X20)
% 0.58/0.78          | (zip_tseitin_0 @ X20 @ X20 @ X18 @ X21 @ X23))),
% 0.58/0.78      inference('simplify', [status(thm)], ['9'])).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A)
% 0.58/0.78          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.78          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.58/0.78          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.58/0.78      inference('sup-', [status(thm)], ['8', '10'])).
% 0.58/0.78  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('13', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A)
% 0.58/0.78          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.58/0.78          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.58/0.78      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((v1_xboole_0 @ sk_B_1)
% 0.58/0.78          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.58/0.78          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['7', '13'])).
% 0.58/0.78  thf('15', plain,
% 0.58/0.78      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C @ sk_B_1 @ sk_A)
% 0.58/0.78        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['1', '14'])).
% 0.58/0.78  thf('16', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.58/0.78  thf(zf_stmt_3, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78       ( ![D:$i]:
% 0.58/0.78         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.58/0.78           ( ![E:$i]:
% 0.58/0.78             ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.78               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.58/0.78         (((X29) != (k5_partfun1 @ X27 @ X26 @ X25))
% 0.58/0.78          | (r2_hidden @ X31 @ X29)
% 0.58/0.78          | ~ (zip_tseitin_0 @ X32 @ X31 @ X25 @ X26 @ X27)
% 0.58/0.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.58/0.78          | ~ (v1_funct_1 @ X25))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.78  thf('18', plain,
% 0.58/0.78      (![X25 : $i, X26 : $i, X27 : $i, X31 : $i, X32 : $i]:
% 0.58/0.78         (~ (v1_funct_1 @ X25)
% 0.58/0.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.58/0.78          | ~ (zip_tseitin_0 @ X32 @ X31 @ X25 @ X26 @ X27)
% 0.58/0.78          | (r2_hidden @ X31 @ (k5_partfun1 @ X27 @ X26 @ X25)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['17'])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))
% 0.58/0.78          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A)
% 0.58/0.78          | ~ (v1_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['16', '18'])).
% 0.58/0.78  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))
% 0.58/0.78          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['19', '20'])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.78        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['15', '21'])).
% 0.58/0.78  thf(l13_xboole_0, axiom,
% 0.58/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.78  thf('26', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          (((X0) != (k1_xboole_0))
% 0.58/0.78           | ~ (v1_xboole_0 @ X0)
% 0.58/0.78           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.58/0.78         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['25', '27'])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.78         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('simplify', [status(thm)], ['28'])).
% 0.58/0.78  thf(d1_xboole_0, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.78  thf(t113_zfmisc_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (![X5 : $i, X6 : $i]:
% 0.58/0.78         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['31'])).
% 0.58/0.78  thf(t152_zfmisc_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.58/0.78  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['29', '35'])).
% 0.58/0.78  thf('37', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('38', plain,
% 0.58/0.78      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_C)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      (((m1_subset_1 @ sk_C @ 
% 0.58/0.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.78  thf(cc1_subset_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_xboole_0 @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.58/0.78          | (v1_xboole_0 @ X9)
% 0.58/0.78          | ~ (v1_xboole_0 @ X10))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.58/0.78         | (v1_xboole_0 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.78  thf('45', plain,
% 0.58/0.78      (![X5 : $i, X6 : $i]:
% 0.58/0.78         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['45'])).
% 0.58/0.78  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.78  thf('48', plain, (((v1_xboole_0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['44', '46', '47'])).
% 0.58/0.78  thf('49', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('50', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('51', plain,
% 0.58/0.78      ((~ (r2_hidden @ sk_D @ 
% 0.58/0.78           (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['39', '50'])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('53', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('54', plain,
% 0.58/0.78      (((m1_subset_1 @ sk_D @ 
% 0.58/0.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['52', '53'])).
% 0.58/0.78  thf('55', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.58/0.78          | (v1_xboole_0 @ X9)
% 0.58/0.78          | ~ (v1_xboole_0 @ X10))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.58/0.78  thf('56', plain,
% 0.58/0.78      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.58/0.78         | (v1_xboole_0 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.78  thf('57', plain,
% 0.58/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['45'])).
% 0.58/0.78  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.78  thf('59', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.58/0.78  thf('60', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('61', plain,
% 0.58/0.78      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.58/0.78  thf('62', plain,
% 0.58/0.78      ((~ (r2_hidden @ k1_xboole_0 @ 
% 0.58/0.78           (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['51', '61'])).
% 0.58/0.78  thf('63', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('64', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('65', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('66', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('67', plain,
% 0.58/0.78      (((r1_partfun1 @ k1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['65', '66'])).
% 0.58/0.78  thf('68', plain,
% 0.58/0.78      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.58/0.78  thf('69', plain,
% 0.58/0.78      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)], ['67', '68'])).
% 0.58/0.78  thf('70', plain,
% 0.58/0.78      ((![X0 : $i]: ((r1_partfun1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['64', '69'])).
% 0.58/0.78  thf('71', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('72', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('73', plain,
% 0.58/0.78      (![X18 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.58/0.78         (~ (r1_partfun1 @ X18 @ X20)
% 0.58/0.78          | ~ (v1_partfun1 @ X20 @ X23)
% 0.58/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.58/0.78          | ~ (v1_funct_1 @ X20)
% 0.58/0.78          | (zip_tseitin_0 @ X20 @ X20 @ X18 @ X21 @ X23))),
% 0.58/0.78      inference('simplify', [status(thm)], ['9'])).
% 0.58/0.78  thf('74', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_B_1 @ sk_A)
% 0.58/0.78          | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.58/0.78          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['72', '73'])).
% 0.58/0.78  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('76', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_B_1 @ sk_A)
% 0.58/0.78          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.58/0.78          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.78  thf('77', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          (~ (v1_partfun1 @ k1_xboole_0 @ sk_A)
% 0.58/0.78           | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.58/0.78           | (zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_B_1 @ sk_A)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['71', '76'])).
% 0.58/0.78  thf('78', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('79', plain,
% 0.58/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['31'])).
% 0.58/0.78  thf(dt_k6_partfun1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( m1_subset_1 @
% 0.58/0.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.58/0.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.58/0.78  thf('80', plain,
% 0.58/0.78      (![X34 : $i]:
% 0.58/0.78         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.58/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.58/0.78  thf('81', plain,
% 0.58/0.78      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['79', '80'])).
% 0.58/0.78  thf('82', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.58/0.78          | (v1_xboole_0 @ X9)
% 0.58/0.78          | ~ (v1_xboole_0 @ X10))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.58/0.78  thf('83', plain,
% 0.58/0.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.78        | (v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.78  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.78  thf('85', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['83', '84'])).
% 0.58/0.78  thf('86', plain,
% 0.58/0.78      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.78  thf('87', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['85', '86'])).
% 0.58/0.78  thf('88', plain, (![X33 : $i]: (v1_partfun1 @ (k6_partfun1 @ X33) @ X33)),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.58/0.78  thf('89', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup+', [status(thm)], ['87', '88'])).
% 0.58/0.78  thf('90', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('91', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('92', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('93', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('94', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.58/0.78           | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B_1 @ 
% 0.58/0.78              k1_xboole_0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['77', '78', '89', '90', '91', '92', '93'])).
% 0.58/0.78  thf('95', plain,
% 0.58/0.78      ((![X0 : $i]:
% 0.58/0.78          (~ (v1_xboole_0 @ X0)
% 0.58/0.78           | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B_1 @ 
% 0.58/0.78              k1_xboole_0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['70', '94'])).
% 0.58/0.78  thf('96', plain,
% 0.58/0.78      ((![X0 : $i, X1 : $i]:
% 0.58/0.78          ((zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_B_1 @ X0)
% 0.58/0.78           | ~ (v1_xboole_0 @ X0)
% 0.58/0.78           | ~ (v1_xboole_0 @ X1)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['63', '95'])).
% 0.58/0.78  thf('97', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))
% 0.58/0.78          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['19', '20'])).
% 0.58/0.78  thf('98', plain,
% 0.58/0.78      (((~ (v1_xboole_0 @ sk_C)
% 0.58/0.78         | ~ (v1_xboole_0 @ sk_A)
% 0.58/0.78         | (r2_hidden @ k1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['96', '97'])).
% 0.58/0.78  thf('99', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.78  thf('101', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.78  thf('103', plain,
% 0.58/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('104', plain,
% 0.58/0.78      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('105', plain,
% 0.58/0.78      (((r2_hidden @ k1_xboole_0 @ 
% 0.58/0.78         (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.58/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['98', '99', '100', '101', '102', '103', '104'])).
% 0.58/0.78  thf('106', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.58/0.78      inference('demod', [status(thm)], ['62', '105'])).
% 0.58/0.78  thf('107', plain,
% 0.58/0.78      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.58/0.78      inference('split', [status(esa)], ['26'])).
% 0.58/0.78  thf('108', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['106', '107'])).
% 0.58/0.78  thf('109', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['36', '108'])).
% 0.58/0.78  thf('110', plain,
% 0.58/0.78      ((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.58/0.78      inference('clc', [status(thm)], ['22', '109'])).
% 0.58/0.78  thf('111', plain, ($false), inference('demod', [status(thm)], ['0', '110'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
