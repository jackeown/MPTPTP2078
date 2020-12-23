%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYznPR09WY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:17 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 865 expanded)
%              Number of leaves         :   32 ( 252 expanded)
%              Depth                    :   18
%              Number of atoms          : 1219 (12666 expanded)
%              Number of equality atoms :  116 ( 761 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X20 @ X23 @ X25 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( X21 != X22 )
      | ~ ( v1_partfun1 @ X21 @ X25 )
      | ~ ( r1_partfun1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X20: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( r1_partfun1 @ X20 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ( zip_tseitin_0 @ X22 @ X22 @ X20 @ X23 @ X25 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i,X33: $i,X34: $i] :
      ( ( X31
       != ( k5_partfun1 @ X29 @ X28 @ X27 ) )
      | ( r2_hidden @ X33 @ X31 )
      | ~ ( zip_tseitin_0 @ X34 @ X33 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X27: $i,X28: $i,X29: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( zip_tseitin_0 @ X34 @ X33 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X33 @ ( k5_partfun1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('58',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( sk_D = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['61'])).

thf('63',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('64',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('69',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['66','74'])).

thf('76',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('77',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','64','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('89',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('100',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( r1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','101'])).

thf('103',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('104',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X20: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( r1_partfun1 @ X20 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ( zip_tseitin_0 @ X22 @ X22 @ X20 @ X23 @ X25 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A )
        | ~ ( r1_partfun1 @ X0 @ sk_C_1 )
        | ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('111',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('112',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('113',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('117',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X35: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('119',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('121',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('122',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('123',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','119','120','121','122','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','124'])).

thf('126',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_B @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('128',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('130',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('131',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('132',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('133',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('136',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('137',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('138',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','135','138'])).

thf('140',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('141',plain,(
    r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['77','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYznPR09WY
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 525 iterations in 0.227s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.47/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.47/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.68  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.47/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.68  thf(t155_funct_2, conjecture,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( ![D:$i]:
% 0.47/0.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68           ( ( r1_partfun1 @ C @ D ) =>
% 0.47/0.68             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.68               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.68        ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68          ( ![D:$i]:
% 0.47/0.68            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.68                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68              ( ( r1_partfun1 @ C @ D ) =>
% 0.47/0.68                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.68                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(d3_tarski, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X1 : $i, X3 : $i]:
% 0.47/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf(d10_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.68  thf('3', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.68      inference('simplify', [status(thm)], ['2'])).
% 0.47/0.68  thf(t3_subset, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X11 : $i, X13 : $i]:
% 0.47/0.68         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.68  thf(t5_subset, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.47/0.68          ( v1_xboole_0 @ C ) ) ))).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X14 @ X15)
% 0.47/0.68          | ~ (v1_xboole_0 @ X16)
% 0.47/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t5_subset])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['1', '7'])).
% 0.47/0.68  thf(t3_xboole_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf(t113_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X9 : $i, X10 : $i]:
% 0.47/0.68         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['11', '13'])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i]:
% 0.47/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('17', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (~ (r1_tarski @ X1 @ X0)
% 0.47/0.68          | ~ (v1_xboole_0 @ X0)
% 0.47/0.68          | ((X1) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))
% 0.47/0.68        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['17', '20'])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.68        | ~ (v1_xboole_0 @ sk_B)
% 0.47/0.68        | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['14', '21'])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (v1_xboole_0 @ X0)
% 0.47/0.68          | ((sk_C_1) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_xboole_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['10', '22'])).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ sk_B)
% 0.47/0.68          | ((sk_C_1) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.68  thf('25', plain, ((~ (v1_xboole_0 @ sk_B) | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.68      inference('condensation', [status(thm)], ['24'])).
% 0.47/0.68  thf('26', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc5_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68       ( ![C:$i]:
% 0.47/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.68             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.47/0.68          | (v1_partfun1 @ X17 @ X18)
% 0.47/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.47/0.68          | ~ (v1_funct_1 @ X17)
% 0.47/0.68          | (v1_xboole_0 @ X19))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.68  thf('29', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.47/0.68        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.68  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('32', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.47/0.68  thf('33', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(d7_partfun1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.68         ( v1_funct_1 @ C ) ) =>
% 0.47/0.68       ( ![D:$i]:
% 0.47/0.68         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.47/0.68           ( ![E:$i]:
% 0.47/0.68             ( ( r2_hidden @ E @ D ) <=>
% 0.47/0.68               ( ?[F:$i]:
% 0.47/0.68                 ( ( v1_funct_1 @ F ) & 
% 0.47/0.68                   ( m1_subset_1 @
% 0.47/0.68                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.68                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.47/0.68                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_1, axiom,
% 0.47/0.68    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.47/0.68     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.47/0.68       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.47/0.68         ( ( F ) = ( E ) ) & 
% 0.47/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.68         ( v1_funct_1 @ F ) ) ))).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ X21 @ X22 @ X20 @ X23 @ X25)
% 0.47/0.68          | ~ (v1_funct_1 @ X21)
% 0.47/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.68          | ((X21) != (X22))
% 0.47/0.68          | ~ (v1_partfun1 @ X21 @ X25)
% 0.47/0.68          | ~ (r1_partfun1 @ X20 @ X21))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.68  thf('35', plain,
% 0.47/0.68      (![X20 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.47/0.68         (~ (r1_partfun1 @ X20 @ X22)
% 0.47/0.68          | ~ (v1_partfun1 @ X22 @ X25)
% 0.47/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.68          | ~ (v1_funct_1 @ X22)
% 0.47/0.68          | (zip_tseitin_0 @ X22 @ X22 @ X20 @ X23 @ X25))),
% 0.47/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.68  thf('36', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_D)
% 0.47/0.68          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.68          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '35'])).
% 0.47/0.68  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.47/0.68          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.47/0.68          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ sk_B)
% 0.47/0.68          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.47/0.68          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['32', '38'])).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ sk_B @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['26', '39'])).
% 0.47/0.68  thf('41', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.47/0.68  thf(zf_stmt_3, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( ![D:$i]:
% 0.47/0.68         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.47/0.68           ( ![E:$i]:
% 0.47/0.68             ( ( r2_hidden @ E @ D ) <=>
% 0.47/0.68               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.47/0.68  thf('42', plain,
% 0.47/0.68      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 0.47/0.68         (((X31) != (k5_partfun1 @ X29 @ X28 @ X27))
% 0.47/0.68          | (r2_hidden @ X33 @ X31)
% 0.47/0.68          | ~ (zip_tseitin_0 @ X34 @ X33 @ X27 @ X28 @ X29)
% 0.47/0.68          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.47/0.68          | ~ (v1_funct_1 @ X27))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      (![X27 : $i, X28 : $i, X29 : $i, X33 : $i, X34 : $i]:
% 0.47/0.68         (~ (v1_funct_1 @ X27)
% 0.47/0.68          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.47/0.68          | ~ (zip_tseitin_0 @ X34 @ X33 @ X27 @ X28 @ X29)
% 0.47/0.68          | (r2_hidden @ X33 @ (k5_partfun1 @ X29 @ X28 @ X27)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.68          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['41', '43'])).
% 0.47/0.68  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.68          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_B)
% 0.47/0.68        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['40', '46'])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('49', plain, ((v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.68  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['25', '49'])).
% 0.47/0.68  thf('51', plain,
% 0.47/0.68      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['0', '50'])).
% 0.47/0.68  thf('52', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('53', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['11', '13'])).
% 0.47/0.68  thf('54', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('55', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i]:
% 0.47/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('56', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.68  thf('57', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (~ (r1_tarski @ X1 @ X0)
% 0.47/0.68          | ~ (v1_xboole_0 @ X0)
% 0.47/0.68          | ((X1) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.68  thf('58', plain,
% 0.47/0.68      ((((sk_D) = (k1_xboole_0))
% 0.47/0.68        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.68  thf('59', plain,
% 0.47/0.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.68        | ~ (v1_xboole_0 @ sk_B)
% 0.47/0.68        | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '58'])).
% 0.47/0.68  thf('60', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (v1_xboole_0 @ X0)
% 0.47/0.68          | ((sk_D) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_xboole_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['52', '59'])).
% 0.47/0.68  thf('61', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ sk_B)
% 0.47/0.68          | ((sk_D) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.68  thf('62', plain, ((~ (v1_xboole_0 @ sk_B) | ((sk_D) = (k1_xboole_0)))),
% 0.47/0.68      inference('condensation', [status(thm)], ['61'])).
% 0.47/0.68  thf('63', plain, ((v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.68  thf('64', plain, (((sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('65', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('66', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('67', plain, ((v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.68  thf('68', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('69', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.68  thf('70', plain,
% 0.47/0.68      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('71', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.47/0.68  thf('72', plain, ((((sk_B) = (k1_xboole_0)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['71'])).
% 0.47/0.68  thf('73', plain, ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('74', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.47/0.68  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['66', '74'])).
% 0.47/0.68  thf('76', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.68  thf('77', plain,
% 0.47/0.68      (~ (r2_hidden @ k1_xboole_0 @ 
% 0.47/0.68          (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['51', '64', '75', '76'])).
% 0.47/0.68  thf('78', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('79', plain,
% 0.47/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('80', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('81', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('82', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_C_1 @ 
% 0.47/0.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['80', '81'])).
% 0.47/0.68  thf('83', plain,
% 0.47/0.68      (![X9 : $i, X10 : $i]:
% 0.47/0.68         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.68  thf('84', plain,
% 0.47/0.68      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['83'])).
% 0.47/0.68  thf('85', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)], ['82', '84'])).
% 0.47/0.68  thf('86', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i]:
% 0.47/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('87', plain,
% 0.47/0.68      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['85', '86'])).
% 0.47/0.68  thf('88', plain,
% 0.47/0.68      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('89', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('90', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('91', plain,
% 0.47/0.68      (((r1_partfun1 @ k1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['89', '90'])).
% 0.47/0.68  thf('92', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('93', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('94', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_D @ 
% 0.47/0.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['92', '93'])).
% 0.47/0.68  thf('95', plain,
% 0.47/0.68      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['83'])).
% 0.47/0.68  thf('96', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)], ['94', '95'])).
% 0.47/0.68  thf('97', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i]:
% 0.47/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('98', plain,
% 0.47/0.68      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['96', '97'])).
% 0.47/0.68  thf('99', plain,
% 0.47/0.68      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('100', plain,
% 0.47/0.68      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('101', plain,
% 0.47/0.68      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)], ['91', '100'])).
% 0.47/0.68  thf('102', plain,
% 0.47/0.68      ((![X0 : $i]: ((r1_partfun1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['79', '101'])).
% 0.47/0.68  thf('103', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('104', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('105', plain,
% 0.47/0.68      (![X20 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.47/0.68         (~ (r1_partfun1 @ X20 @ X22)
% 0.47/0.68          | ~ (v1_partfun1 @ X22 @ X25)
% 0.47/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.47/0.68          | ~ (v1_funct_1 @ X22)
% 0.47/0.68          | (zip_tseitin_0 @ X22 @ X22 @ X20 @ X23 @ X25))),
% 0.47/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.68  thf('106', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_C_1)
% 0.47/0.68          | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.47/0.68          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['104', '105'])).
% 0.47/0.68  thf('107', plain, ((v1_funct_1 @ sk_C_1)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('108', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A)
% 0.47/0.68          | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.47/0.68          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.47/0.68      inference('demod', [status(thm)], ['106', '107'])).
% 0.47/0.68  thf('109', plain,
% 0.47/0.68      ((![X0 : $i]:
% 0.47/0.68          (~ (v1_partfun1 @ k1_xboole_0 @ sk_A)
% 0.47/0.68           | ~ (r1_partfun1 @ X0 @ sk_C_1)
% 0.47/0.68           | (zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['103', '108'])).
% 0.47/0.68  thf('110', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('111', plain,
% 0.47/0.68      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.47/0.68  thf(dt_k6_partfun1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( m1_subset_1 @
% 0.47/0.68         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.68       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.68  thf('112', plain,
% 0.47/0.68      (![X36 : $i]:
% 0.47/0.68         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.47/0.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.68  thf('113', plain,
% 0.47/0.68      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['111', '112'])).
% 0.47/0.68  thf('114', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i]:
% 0.47/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('115', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.47/0.68      inference('sup-', [status(thm)], ['113', '114'])).
% 0.47/0.68  thf('116', plain,
% 0.47/0.68      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('117', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['115', '116'])).
% 0.47/0.68  thf('118', plain, (![X35 : $i]: (v1_partfun1 @ (k6_partfun1 @ X35) @ X35)),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.68  thf('119', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.68      inference('sup+', [status(thm)], ['117', '118'])).
% 0.47/0.68  thf('120', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('121', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('122', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('123', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('124', plain,
% 0.47/0.68      ((![X0 : $i]:
% 0.47/0.68          (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.47/0.68           | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ 
% 0.47/0.68              k1_xboole_0)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)],
% 0.47/0.68                ['109', '110', '119', '120', '121', '122', '123'])).
% 0.47/0.68  thf('125', plain,
% 0.47/0.68      ((![X0 : $i]:
% 0.47/0.68          (~ (v1_xboole_0 @ X0)
% 0.47/0.68           | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ 
% 0.47/0.68              k1_xboole_0)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['102', '124'])).
% 0.47/0.68  thf('126', plain,
% 0.47/0.68      ((![X0 : $i, X1 : $i]:
% 0.47/0.68          ((zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_B @ X0)
% 0.47/0.68           | ~ (v1_xboole_0 @ X0)
% 0.47/0.68           | ~ (v1_xboole_0 @ X1)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['78', '125'])).
% 0.47/0.68  thf('127', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.68          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.68  thf('128', plain,
% 0.47/0.68      (((~ (v1_xboole_0 @ sk_C_1)
% 0.47/0.68         | ~ (v1_xboole_0 @ sk_A)
% 0.47/0.68         | (r2_hidden @ k1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['126', '127'])).
% 0.47/0.68  thf('129', plain,
% 0.47/0.68      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('130', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['65'])).
% 0.47/0.68  thf('131', plain,
% 0.47/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('split', [status(esa)], ['65'])).
% 0.47/0.69  thf('132', plain,
% 0.47/0.69      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.69  thf('133', plain,
% 0.47/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.69         | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.69         | (r2_hidden @ k1_xboole_0 @ 
% 0.47/0.69            (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))))
% 0.47/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.47/0.69  thf('134', plain,
% 0.47/0.69      ((((r2_hidden @ k1_xboole_0 @ 
% 0.47/0.69          (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))
% 0.47/0.69         | ~ (v1_xboole_0 @ k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.69  thf('135', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.69  thf('136', plain, ((v1_xboole_0 @ sk_B)),
% 0.47/0.69      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.69  thf('137', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.69  thf('138', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['136', '137'])).
% 0.47/0.69  thf('139', plain,
% 0.47/0.69      (((r2_hidden @ k1_xboole_0 @ 
% 0.47/0.69         (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.47/0.69         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.69      inference('demod', [status(thm)], ['134', '135', '138'])).
% 0.47/0.69  thf('140', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.47/0.69      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.47/0.69  thf('141', plain,
% 0.47/0.69      ((r2_hidden @ k1_xboole_0 @ 
% 0.47/0.69        (k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 0.47/0.69  thf('142', plain, ($false), inference('demod', [status(thm)], ['77', '141'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.56/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
