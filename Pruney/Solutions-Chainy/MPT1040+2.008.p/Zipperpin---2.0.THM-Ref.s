%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EJt0OCNwCU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:17 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 389 expanded)
%              Number of leaves         :   34 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          : 1111 (4108 expanded)
%              Number of equality atoms :   89 ( 334 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X23 @ X26 @ X28 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( X24 != X25 )
      | ~ ( v1_partfun1 @ X24 @ X28 )
      | ~ ( r1_partfun1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X23: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( r1_partfun1 @ X23 @ X25 )
      | ~ ( v1_partfun1 @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( zip_tseitin_0 @ X25 @ X25 @ X23 @ X26 @ X28 ) ) ),
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
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ sk_B_1 @ sk_A_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X34: $i,X36: $i,X37: $i] :
      ( ( X34
       != ( k5_partfun1 @ X32 @ X31 @ X30 ) )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( zip_tseitin_0 @ X37 @ X36 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( zip_tseitin_0 @ X37 @ X36 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X36 @ ( k5_partfun1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B_1 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
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
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
      | ( k1_xboole_0 = sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('54',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('57',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('58',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('68',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('71',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('74',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('76',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('83',plain,(
    ! [X23: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( r1_partfun1 @ X23 @ X25 )
      | ~ ( v1_partfun1 @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( zip_tseitin_0 @ X25 @ X25 @ X23 @ X26 @ X28 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ X1 @ X1 @ X2 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( r1_partfun1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('88',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('89',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('90',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','94'])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('97',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X38: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X38 ) @ X38 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('99',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','99'])).

thf('101',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X1 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('104',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('107',plain,(
    ! [X30: $i,X31: $i,X32: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( zip_tseitin_0 @ X37 @ X36 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X36 @ ( k5_partfun1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X2 @ ( k5_partfun1 @ k1_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['69','113'])).

thf('115',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('116',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['35','116'])).

thf('118',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['22','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EJt0OCNwCU
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:46:08 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.65/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.65/0.82  % Solved by: fo/fo7.sh
% 0.65/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.82  % done 762 iterations in 0.328s
% 0.65/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.65/0.82  % SZS output start Refutation
% 0.65/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.65/0.82  thf(sk_D_type, type, sk_D: $i).
% 0.65/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.82  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.65/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.65/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.65/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.82  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.65/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.65/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.82  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.65/0.82  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.65/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.82  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.65/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.65/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.65/0.82  thf(t155_funct_2, conjecture,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.82       ( ![D:$i]:
% 0.65/0.82         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.65/0.82             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.82           ( ( r1_partfun1 @ C @ D ) =>
% 0.65/0.82             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.65/0.82               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.65/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.65/0.82        ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.82          ( ![D:$i]:
% 0.65/0.82            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.65/0.82                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.82              ( ( r1_partfun1 @ C @ D ) =>
% 0.65/0.82                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.65/0.82                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.65/0.82    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.65/0.82  thf('0', plain,
% 0.65/0.82      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('1', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('2', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(cc5_funct_2, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.65/0.82       ( ![C:$i]:
% 0.65/0.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.82           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.65/0.82             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.65/0.82  thf('3', plain,
% 0.65/0.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.65/0.82         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.65/0.82          | (v1_partfun1 @ X20 @ X21)
% 0.65/0.82          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.65/0.82          | ~ (v1_funct_1 @ X20)
% 0.65/0.82          | (v1_xboole_0 @ X22))),
% 0.65/0.82      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.65/0.82  thf('4', plain,
% 0.65/0.82      (((v1_xboole_0 @ sk_B_1)
% 0.65/0.82        | ~ (v1_funct_1 @ sk_D)
% 0.65/0.82        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1)
% 0.65/0.82        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.65/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.65/0.82  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B_1)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.65/0.82      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.65/0.82  thf('8', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(d7_partfun1, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.65/0.82         ( v1_funct_1 @ C ) ) =>
% 0.65/0.82       ( ![D:$i]:
% 0.65/0.82         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.65/0.82           ( ![E:$i]:
% 0.65/0.82             ( ( r2_hidden @ E @ D ) <=>
% 0.65/0.82               ( ?[F:$i]:
% 0.65/0.82                 ( ( v1_funct_1 @ F ) & 
% 0.65/0.82                   ( m1_subset_1 @
% 0.65/0.82                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.65/0.82                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.65/0.82                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.65/0.82  thf(zf_stmt_1, axiom,
% 0.65/0.82    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.65/0.82     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.65/0.82       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.65/0.82         ( ( F ) = ( E ) ) & 
% 0.65/0.82         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.65/0.82         ( v1_funct_1 @ F ) ) ))).
% 0.65/0.82  thf('9', plain,
% 0.65/0.82      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.65/0.82         ((zip_tseitin_0 @ X24 @ X25 @ X23 @ X26 @ X28)
% 0.65/0.82          | ~ (v1_funct_1 @ X24)
% 0.65/0.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.65/0.82          | ((X24) != (X25))
% 0.65/0.82          | ~ (v1_partfun1 @ X24 @ X28)
% 0.65/0.82          | ~ (r1_partfun1 @ X23 @ X24))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.65/0.82  thf('10', plain,
% 0.65/0.82      (![X23 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.65/0.82         (~ (r1_partfun1 @ X23 @ X25)
% 0.65/0.82          | ~ (v1_partfun1 @ X25 @ X28)
% 0.65/0.82          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.65/0.82          | ~ (v1_funct_1 @ X25)
% 0.65/0.82          | (zip_tseitin_0 @ X25 @ X25 @ X23 @ X26 @ X28))),
% 0.65/0.82      inference('simplify', [status(thm)], ['9'])).
% 0.65/0.82  thf('11', plain,
% 0.65/0.82      (![X0 : $i]:
% 0.65/0.82         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1)
% 0.65/0.82          | ~ (v1_funct_1 @ sk_D)
% 0.65/0.82          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.65/0.82          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.65/0.82      inference('sup-', [status(thm)], ['8', '10'])).
% 0.65/0.82  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('13', plain,
% 0.65/0.82      (![X0 : $i]:
% 0.65/0.82         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1)
% 0.65/0.82          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.65/0.82          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.65/0.82      inference('demod', [status(thm)], ['11', '12'])).
% 0.65/0.82  thf('14', plain,
% 0.65/0.82      (![X0 : $i]:
% 0.65/0.82         ((v1_xboole_0 @ sk_B_1)
% 0.65/0.82          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.65/0.82          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B_1 @ sk_A_1))),
% 0.65/0.82      inference('sup-', [status(thm)], ['7', '13'])).
% 0.65/0.82  thf('15', plain,
% 0.65/0.82      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.65/0.82        | (v1_xboole_0 @ sk_B_1))),
% 0.65/0.82      inference('sup-', [status(thm)], ['1', '14'])).
% 0.65/0.82  thf('16', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.65/0.82  thf(zf_stmt_3, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( ( v1_funct_1 @ C ) & 
% 0.65/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.82       ( ![D:$i]:
% 0.65/0.82         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.65/0.82           ( ![E:$i]:
% 0.65/0.82             ( ( r2_hidden @ E @ D ) <=>
% 0.65/0.82               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.65/0.82  thf('17', plain,
% 0.65/0.82      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i, X36 : $i, X37 : $i]:
% 0.65/0.82         (((X34) != (k5_partfun1 @ X32 @ X31 @ X30))
% 0.65/0.82          | (r2_hidden @ X36 @ X34)
% 0.65/0.82          | ~ (zip_tseitin_0 @ X37 @ X36 @ X30 @ X31 @ X32)
% 0.65/0.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.65/0.82          | ~ (v1_funct_1 @ X30))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.65/0.82  thf('18', plain,
% 0.65/0.82      (![X30 : $i, X31 : $i, X32 : $i, X36 : $i, X37 : $i]:
% 0.65/0.82         (~ (v1_funct_1 @ X30)
% 0.65/0.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.65/0.82          | ~ (zip_tseitin_0 @ X37 @ X36 @ X30 @ X31 @ X32)
% 0.65/0.82          | (r2_hidden @ X36 @ (k5_partfun1 @ X32 @ X31 @ X30)))),
% 0.65/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.65/0.82  thf('19', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.65/0.82          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B_1 @ sk_A_1)
% 0.65/0.82          | ~ (v1_funct_1 @ sk_C_1))),
% 0.65/0.82      inference('sup-', [status(thm)], ['16', '18'])).
% 0.65/0.82  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('21', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.65/0.82          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B_1 @ sk_A_1))),
% 0.65/0.82      inference('demod', [status(thm)], ['19', '20'])).
% 0.65/0.82  thf('22', plain,
% 0.65/0.82      (((v1_xboole_0 @ sk_B_1)
% 0.65/0.82        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['15', '21'])).
% 0.65/0.82  thf(l13_xboole_0, axiom,
% 0.65/0.82    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.65/0.82  thf('23', plain,
% 0.65/0.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.65/0.82      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.65/0.82  thf('24', plain,
% 0.65/0.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.65/0.82      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.65/0.82  thf('25', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.65/0.82      inference('sup+', [status(thm)], ['23', '24'])).
% 0.65/0.82  thf('26', plain,
% 0.65/0.82      ((((sk_B_1) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('27', plain,
% 0.65/0.82      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('split', [status(esa)], ['26'])).
% 0.65/0.82  thf('28', plain,
% 0.65/0.82      ((![X0 : $i]:
% 0.65/0.82          (((X0) != (k1_xboole_0))
% 0.65/0.82           | ~ (v1_xboole_0 @ X0)
% 0.65/0.82           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.65/0.82         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['25', '27'])).
% 0.65/0.82  thf('29', plain,
% 0.65/0.82      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.65/0.82         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('simplify', [status(thm)], ['28'])).
% 0.65/0.82  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.65/0.82  thf('30', plain, ((v1_xboole_0 @ sk_A)),
% 0.65/0.82      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.65/0.82  thf('31', plain, ((v1_xboole_0 @ sk_A)),
% 0.65/0.82      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.65/0.82  thf('32', plain,
% 0.65/0.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.65/0.82      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.65/0.82  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['31', '32'])).
% 0.65/0.82  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.65/0.82      inference('demod', [status(thm)], ['30', '33'])).
% 0.65/0.82  thf('35', plain,
% 0.65/0.82      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('simplify_reflect+', [status(thm)], ['29', '34'])).
% 0.65/0.82  thf('36', plain,
% 0.65/0.82      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('split', [status(esa)], ['26'])).
% 0.65/0.82  thf('37', plain,
% 0.65/0.82      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('38', plain,
% 0.65/0.82      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.82  thf(d3_tarski, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.65/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.65/0.82  thf('39', plain,
% 0.65/0.82      (![X4 : $i, X6 : $i]:
% 0.65/0.82         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.65/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.65/0.82  thf(d1_xboole_0, axiom,
% 0.65/0.82    (![A:$i]:
% 0.65/0.82     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.65/0.82  thf('40', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.65/0.82      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.65/0.82  thf('41', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.65/0.82  thf(t113_zfmisc_1, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.65/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.65/0.82  thf('42', plain,
% 0.65/0.82      (![X12 : $i, X13 : $i]:
% 0.65/0.82         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.65/0.82          | ((X12) != (k1_xboole_0)))),
% 0.65/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.82  thf('43', plain,
% 0.65/0.82      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.82  thf('44', plain,
% 0.65/0.82      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('split', [status(esa)], ['26'])).
% 0.65/0.82  thf('45', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('46', plain,
% 0.65/0.82      (((m1_subset_1 @ sk_C_1 @ 
% 0.65/0.82         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.82  thf('47', plain,
% 0.65/0.82      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup+', [status(thm)], ['43', '46'])).
% 0.65/0.82  thf(t3_subset, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.82  thf('48', plain,
% 0.65/0.82      (![X14 : $i, X15 : $i]:
% 0.65/0.82         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.65/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.82  thf('49', plain,
% 0.65/0.82      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['47', '48'])).
% 0.65/0.82  thf(d10_xboole_0, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.65/0.82  thf('50', plain,
% 0.65/0.82      (![X8 : $i, X10 : $i]:
% 0.65/0.82         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.65/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.65/0.82  thf('51', plain,
% 0.65/0.82      (((~ (r1_tarski @ k1_xboole_0 @ sk_C_1) | ((k1_xboole_0) = (sk_C_1))))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['49', '50'])).
% 0.65/0.82  thf('52', plain,
% 0.65/0.82      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_C_1))))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['41', '51'])).
% 0.65/0.82  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.65/0.82      inference('demod', [status(thm)], ['30', '33'])).
% 0.65/0.82  thf('54', plain,
% 0.65/0.82      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.82  thf('55', plain,
% 0.65/0.82      ((~ (r2_hidden @ sk_D @ 
% 0.65/0.82           (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['38', '54'])).
% 0.65/0.82  thf('56', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.65/0.82  thf('57', plain,
% 0.65/0.82      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.82  thf('58', plain,
% 0.65/0.82      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('split', [status(esa)], ['26'])).
% 0.65/0.82  thf('59', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('60', plain,
% 0.65/0.82      (((m1_subset_1 @ sk_D @ 
% 0.65/0.82         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup+', [status(thm)], ['58', '59'])).
% 0.65/0.82  thf('61', plain,
% 0.65/0.82      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup+', [status(thm)], ['57', '60'])).
% 0.65/0.82  thf('62', plain,
% 0.65/0.82      (![X14 : $i, X15 : $i]:
% 0.65/0.82         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.65/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.82  thf('63', plain,
% 0.65/0.82      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['61', '62'])).
% 0.65/0.82  thf('64', plain,
% 0.65/0.82      (![X8 : $i, X10 : $i]:
% 0.65/0.82         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.65/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.65/0.82  thf('65', plain,
% 0.65/0.82      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['63', '64'])).
% 0.65/0.82  thf('66', plain,
% 0.65/0.82      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D))))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['56', '65'])).
% 0.65/0.82  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.65/0.82      inference('demod', [status(thm)], ['30', '33'])).
% 0.65/0.82  thf('68', plain,
% 0.65/0.82      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['66', '67'])).
% 0.65/0.82  thf('69', plain,
% 0.65/0.82      ((~ (r2_hidden @ k1_xboole_0 @ 
% 0.65/0.82           (k5_partfun1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['55', '68'])).
% 0.65/0.82  thf('70', plain,
% 0.65/0.82      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.82  thf('71', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('72', plain,
% 0.65/0.82      (((r1_partfun1 @ k1_xboole_0 @ sk_D)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup+', [status(thm)], ['70', '71'])).
% 0.65/0.82  thf('73', plain,
% 0.65/0.82      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['66', '67'])).
% 0.65/0.82  thf('74', plain,
% 0.65/0.82      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['72', '73'])).
% 0.65/0.82  thf('75', plain,
% 0.65/0.82      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.82  thf('76', plain, ((v1_funct_1 @ sk_C_1)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('77', plain,
% 0.65/0.82      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup+', [status(thm)], ['75', '76'])).
% 0.65/0.82  thf('78', plain,
% 0.65/0.82      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.65/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.65/0.82  thf('79', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.65/0.82      inference('simplify', [status(thm)], ['78'])).
% 0.65/0.82  thf('80', plain,
% 0.65/0.82      (![X14 : $i, X16 : $i]:
% 0.65/0.82         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.65/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.82  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['79', '80'])).
% 0.65/0.82  thf('82', plain,
% 0.65/0.82      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.82  thf('83', plain,
% 0.65/0.82      (![X23 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.65/0.82         (~ (r1_partfun1 @ X23 @ X25)
% 0.65/0.82          | ~ (v1_partfun1 @ X25 @ X28)
% 0.65/0.82          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.65/0.82          | ~ (v1_funct_1 @ X25)
% 0.65/0.82          | (zip_tseitin_0 @ X25 @ X25 @ X23 @ X26 @ X28))),
% 0.65/0.82      inference('simplify', [status(thm)], ['9'])).
% 0.65/0.82  thf('84', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.65/0.82          | (zip_tseitin_0 @ X1 @ X1 @ X2 @ X0 @ k1_xboole_0)
% 0.65/0.82          | ~ (v1_funct_1 @ X1)
% 0.65/0.82          | ~ (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.65/0.82          | ~ (r1_partfun1 @ X2 @ X1))),
% 0.65/0.82      inference('sup-', [status(thm)], ['82', '83'])).
% 0.65/0.82  thf('85', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.65/0.82          | ~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.65/0.82          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.65/0.82          | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['81', '84'])).
% 0.65/0.82  thf('86', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.65/0.82  thf('87', plain,
% 0.65/0.82      (![X12 : $i, X13 : $i]:
% 0.65/0.82         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.65/0.82          | ((X13) != (k1_xboole_0)))),
% 0.65/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.65/0.82  thf('88', plain,
% 0.65/0.82      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['87'])).
% 0.65/0.82  thf(dt_k6_partfun1, axiom,
% 0.65/0.82    (![A:$i]:
% 0.65/0.82     ( ( m1_subset_1 @
% 0.65/0.82         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.65/0.82       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.65/0.82  thf('89', plain,
% 0.65/0.82      (![X39 : $i]:
% 0.65/0.82         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 0.65/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 0.65/0.82      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.65/0.82  thf('90', plain,
% 0.65/0.82      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.65/0.82      inference('sup+', [status(thm)], ['88', '89'])).
% 0.65/0.82  thf('91', plain,
% 0.65/0.82      (![X14 : $i, X15 : $i]:
% 0.65/0.82         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.65/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.82  thf('92', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.65/0.82      inference('sup-', [status(thm)], ['90', '91'])).
% 0.65/0.82  thf('93', plain,
% 0.65/0.82      (![X8 : $i, X10 : $i]:
% 0.65/0.82         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.65/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.65/0.82  thf('94', plain,
% 0.65/0.82      ((~ (r1_tarski @ k1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))
% 0.65/0.82        | ((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['92', '93'])).
% 0.65/0.82  thf('95', plain,
% 0.65/0.82      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.65/0.82        | ((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['86', '94'])).
% 0.65/0.82  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.65/0.82      inference('demod', [status(thm)], ['30', '33'])).
% 0.65/0.82  thf('97', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.65/0.82      inference('demod', [status(thm)], ['95', '96'])).
% 0.65/0.82  thf('98', plain, (![X38 : $i]: (v1_partfun1 @ (k6_partfun1 @ X38) @ X38)),
% 0.65/0.82      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.65/0.82  thf('99', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.65/0.82      inference('sup+', [status(thm)], ['97', '98'])).
% 0.65/0.82  thf('100', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.65/0.82          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.65/0.82          | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ X1 @ k1_xboole_0))),
% 0.65/0.82      inference('demod', [status(thm)], ['85', '99'])).
% 0.65/0.82  thf('101', plain,
% 0.65/0.82      ((![X0 : $i, X1 : $i]:
% 0.65/0.82          ((zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 @ k1_xboole_0)
% 0.65/0.82           | ~ (r1_partfun1 @ X1 @ k1_xboole_0)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['77', '100'])).
% 0.65/0.82  thf('102', plain,
% 0.65/0.82      ((![X0 : $i]:
% 0.65/0.82          (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ 
% 0.65/0.82           k1_xboole_0))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['74', '101'])).
% 0.65/0.82  thf('103', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.65/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.65/0.82  thf('104', plain,
% 0.65/0.82      (![X14 : $i, X16 : $i]:
% 0.65/0.82         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.65/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.65/0.82  thf('105', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['103', '104'])).
% 0.65/0.82  thf('106', plain,
% 0.65/0.82      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.82  thf('107', plain,
% 0.65/0.82      (![X30 : $i, X31 : $i, X32 : $i, X36 : $i, X37 : $i]:
% 0.65/0.82         (~ (v1_funct_1 @ X30)
% 0.65/0.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.65/0.82          | ~ (zip_tseitin_0 @ X37 @ X36 @ X30 @ X31 @ X32)
% 0.65/0.82          | (r2_hidden @ X36 @ (k5_partfun1 @ X32 @ X31 @ X30)))),
% 0.65/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.65/0.82  thf('108', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.65/0.82          | (r2_hidden @ X2 @ (k5_partfun1 @ k1_xboole_0 @ X0 @ X1))
% 0.65/0.82          | ~ (zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 0.65/0.82          | ~ (v1_funct_1 @ X1))),
% 0.65/0.82      inference('sup-', [status(thm)], ['106', '107'])).
% 0.65/0.82  thf('109', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.82         (~ (v1_xboole_0 @ X0)
% 0.65/0.82          | ~ (v1_funct_1 @ X0)
% 0.65/0.82          | ~ (zip_tseitin_0 @ X3 @ X2 @ X0 @ X1 @ k1_xboole_0)
% 0.65/0.82          | (r2_hidden @ X2 @ (k5_partfun1 @ k1_xboole_0 @ X1 @ X0)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['105', '108'])).
% 0.65/0.82  thf('110', plain,
% 0.65/0.82      ((![X0 : $i]:
% 0.65/0.82          ((r2_hidden @ k1_xboole_0 @ 
% 0.65/0.82            (k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 0.65/0.82           | ~ (v1_funct_1 @ k1_xboole_0)
% 0.65/0.82           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.65/0.82         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.83      inference('sup-', [status(thm)], ['102', '109'])).
% 0.65/0.83  thf('111', plain,
% 0.65/0.83      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.83      inference('sup+', [status(thm)], ['75', '76'])).
% 0.65/0.83  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.65/0.83      inference('demod', [status(thm)], ['30', '33'])).
% 0.65/0.83  thf('113', plain,
% 0.65/0.83      ((![X0 : $i]:
% 0.65/0.83          (r2_hidden @ k1_xboole_0 @ 
% 0.65/0.83           (k5_partfun1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))
% 0.65/0.83         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.65/0.83      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.65/0.83  thf('114', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.65/0.83      inference('demod', [status(thm)], ['69', '113'])).
% 0.65/0.83  thf('115', plain,
% 0.65/0.83      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.65/0.83      inference('split', [status(esa)], ['26'])).
% 0.65/0.83  thf('116', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.65/0.83      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 0.65/0.83  thf('117', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.65/0.83      inference('simpl_trail', [status(thm)], ['35', '116'])).
% 0.65/0.83  thf('118', plain,
% 0.65/0.83      ((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A_1 @ sk_B_1 @ sk_C_1))),
% 0.65/0.83      inference('clc', [status(thm)], ['22', '117'])).
% 0.65/0.83  thf('119', plain, ($false), inference('demod', [status(thm)], ['0', '118'])).
% 0.65/0.83  
% 0.65/0.83  % SZS output end Refutation
% 0.65/0.83  
% 0.65/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
