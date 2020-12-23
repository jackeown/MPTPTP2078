%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Lk1TAItQ3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:40 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  203 (3780 expanded)
%              Number of leaves         :   38 (1028 expanded)
%              Depth                    :   29
%              Number of atoms          : 1686 (66249 expanded)
%              Number of equality atoms :  157 (5020 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 )
        = ( k7_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('61',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('70',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('72',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('81',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('83',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ sk_D )
         != ( k1_relat_1 @ sk_D ) )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ ( k1_relat_1 @ sk_D ) )
        | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ X0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('94',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('99',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('100',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('105',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('106',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','111'])).

thf('113',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','111'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','112','113','114'])).

thf('116',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['70','75','76','77','78','79','80','115'])).

thf('117',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('118',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','119'])).

thf('121',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('126',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['18','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('141',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','144'])).

thf('146',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['15','145'])).

thf('147',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','144'])).

thf('148',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('149',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['18','133'])).

thf('151',plain,
    ( ( k1_relset_1 @ sk_C @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('153',plain,
    ( ( sk_C != sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('156',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','144'])).

thf('157',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('158',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','118'])).

thf('161',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['154','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['146','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Lk1TAItQ3
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.43/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.43/1.64  % Solved by: fo/fo7.sh
% 1.43/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.64  % done 1007 iterations in 1.188s
% 1.43/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.43/1.64  % SZS output start Refutation
% 1.43/1.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.43/1.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.43/1.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.43/1.64  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.43/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.43/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.43/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.43/1.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.43/1.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.43/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.43/1.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.43/1.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.43/1.64  thf(sk_D_type, type, sk_D: $i).
% 1.43/1.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.43/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.43/1.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.43/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.43/1.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.43/1.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.43/1.64  thf(t38_funct_2, conjecture,
% 1.43/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.43/1.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.64       ( ( r1_tarski @ C @ A ) =>
% 1.43/1.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.43/1.64           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 1.43/1.64             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 1.43/1.64             ( m1_subset_1 @
% 1.43/1.64               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 1.43/1.64               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 1.43/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.43/1.64            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.64          ( ( r1_tarski @ C @ A ) =>
% 1.43/1.64            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.43/1.64              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 1.43/1.64                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 1.43/1.64                ( m1_subset_1 @
% 1.43/1.64                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 1.43/1.64                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 1.43/1.64    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 1.43/1.64  thf('0', plain,
% 1.43/1.64      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 1.43/1.64        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 1.43/1.64             sk_B)
% 1.43/1.64        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 1.43/1.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('1', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf(redefinition_k2_partfun1, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.64     ( ( ( v1_funct_1 @ C ) & 
% 1.43/1.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.64       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.43/1.64  thf('2', plain,
% 1.43/1.64      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.43/1.64          | ~ (v1_funct_1 @ X36)
% 1.43/1.64          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 1.43/1.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.43/1.64  thf('3', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 1.43/1.64          | ~ (v1_funct_1 @ sk_D))),
% 1.43/1.64      inference('sup-', [status(thm)], ['1', '2'])).
% 1.43/1.64  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('5', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['3', '4'])).
% 1.43/1.64  thf('6', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf(dt_k2_partfun1, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.64     ( ( ( v1_funct_1 @ C ) & 
% 1.43/1.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.64       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 1.43/1.64         ( m1_subset_1 @
% 1.43/1.64           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 1.43/1.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.43/1.64  thf('7', plain,
% 1.43/1.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.43/1.64          | ~ (v1_funct_1 @ X32)
% 1.43/1.64          | (v1_funct_1 @ (k2_partfun1 @ X33 @ X34 @ X32 @ X35)))),
% 1.43/1.64      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 1.43/1.64  thf('8', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 1.43/1.64          | ~ (v1_funct_1 @ sk_D))),
% 1.43/1.64      inference('sup-', [status(thm)], ['6', '7'])).
% 1.43/1.64  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('10', plain,
% 1.43/1.64      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['8', '9'])).
% 1.43/1.64  thf('11', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['3', '4'])).
% 1.43/1.64  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['10', '11'])).
% 1.43/1.64  thf('13', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['3', '4'])).
% 1.43/1.64  thf('14', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['3', '4'])).
% 1.43/1.64  thf('15', plain,
% 1.43/1.64      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 1.43/1.64        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 1.43/1.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 1.43/1.64      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 1.43/1.64  thf(d10_xboole_0, axiom,
% 1.43/1.64    (![A:$i,B:$i]:
% 1.43/1.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.43/1.64  thf('16', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.43/1.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.43/1.64  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.43/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.43/1.64  thf('18', plain, ((r1_tarski @ sk_C @ sk_A)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.43/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.43/1.64  thf('20', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf(t13_relset_1, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.64     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.43/1.64       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.43/1.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.43/1.64  thf('21', plain,
% 1.43/1.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.43/1.64         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.43/1.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.43/1.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.43/1.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.43/1.64  thf('22', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.43/1.64          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 1.43/1.64      inference('sup-', [status(thm)], ['20', '21'])).
% 1.43/1.64  thf('23', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ 
% 1.43/1.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['19', '22'])).
% 1.43/1.64  thf(cc2_relset_1, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i]:
% 1.43/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.43/1.64  thf('24', plain,
% 1.43/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.43/1.64         ((v4_relat_1 @ X14 @ X15)
% 1.43/1.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.43/1.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.43/1.64  thf('25', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 1.43/1.64      inference('sup-', [status(thm)], ['23', '24'])).
% 1.43/1.64  thf(t209_relat_1, axiom,
% 1.43/1.64    (![A:$i,B:$i]:
% 1.43/1.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.43/1.64       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.43/1.64  thf('26', plain,
% 1.43/1.64      (![X7 : $i, X8 : $i]:
% 1.43/1.64         (((X7) = (k7_relat_1 @ X7 @ X8))
% 1.43/1.64          | ~ (v4_relat_1 @ X7 @ X8)
% 1.43/1.64          | ~ (v1_relat_1 @ X7))),
% 1.43/1.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.43/1.64  thf('27', plain,
% 1.43/1.64      ((~ (v1_relat_1 @ sk_D)
% 1.43/1.64        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['25', '26'])).
% 1.43/1.64  thf('28', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf(cc1_relset_1, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i]:
% 1.43/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.64       ( v1_relat_1 @ C ) ))).
% 1.43/1.64  thf('29', plain,
% 1.43/1.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.43/1.64         ((v1_relat_1 @ X11)
% 1.43/1.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.43/1.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.43/1.64  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 1.43/1.64      inference('sup-', [status(thm)], ['28', '29'])).
% 1.43/1.64  thf('31', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('demod', [status(thm)], ['27', '30'])).
% 1.43/1.64  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.43/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.43/1.64  thf(t91_relat_1, axiom,
% 1.43/1.64    (![A:$i,B:$i]:
% 1.43/1.64     ( ( v1_relat_1 @ B ) =>
% 1.43/1.64       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.43/1.64         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.43/1.64  thf('33', plain,
% 1.43/1.64      (![X9 : $i, X10 : $i]:
% 1.43/1.64         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 1.43/1.64          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 1.43/1.64          | ~ (v1_relat_1 @ X10))),
% 1.43/1.64      inference('cnf', [status(esa)], [t91_relat_1])).
% 1.43/1.64  thf('34', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (~ (v1_relat_1 @ X0)
% 1.43/1.64          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 1.43/1.64              = (k1_relat_1 @ X0)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['32', '33'])).
% 1.43/1.64  thf('35', plain,
% 1.43/1.64      (![X9 : $i, X10 : $i]:
% 1.43/1.64         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 1.43/1.64          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 1.43/1.64          | ~ (v1_relat_1 @ X10))),
% 1.43/1.64      inference('cnf', [status(esa)], [t91_relat_1])).
% 1.43/1.64  thf('36', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         (~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 1.43/1.64          | ~ (v1_relat_1 @ X0)
% 1.43/1.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 1.43/1.64          | ((k1_relat_1 @ 
% 1.43/1.64              (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1)) = (
% 1.43/1.64              X1)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['34', '35'])).
% 1.43/1.64  thf('37', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (~ (v1_relat_1 @ sk_D)
% 1.43/1.64          | ((k1_relat_1 @ 
% 1.43/1.64              (k7_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) @ X0))
% 1.43/1.64              = (X0))
% 1.43/1.64          | ~ (v1_relat_1 @ sk_D)
% 1.43/1.64          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['31', '36'])).
% 1.43/1.64  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 1.43/1.64      inference('sup-', [status(thm)], ['28', '29'])).
% 1.43/1.64  thf('39', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('demod', [status(thm)], ['27', '30'])).
% 1.43/1.64  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 1.43/1.64      inference('sup-', [status(thm)], ['28', '29'])).
% 1.43/1.64  thf('41', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))
% 1.43/1.64          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 1.43/1.64  thf(d1_funct_2, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i]:
% 1.43/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.43/1.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.43/1.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.43/1.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.43/1.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.43/1.64  thf(zf_stmt_1, axiom,
% 1.43/1.64    (![B:$i,A:$i]:
% 1.43/1.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.43/1.64       ( zip_tseitin_0 @ B @ A ) ))).
% 1.43/1.64  thf('42', plain,
% 1.43/1.64      (![X24 : $i, X25 : $i]:
% 1.43/1.64         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.64  thf(t113_zfmisc_1, axiom,
% 1.43/1.64    (![A:$i,B:$i]:
% 1.43/1.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.43/1.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.43/1.64  thf('43', plain,
% 1.43/1.64      (![X5 : $i, X6 : $i]:
% 1.43/1.64         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.64  thf('44', plain,
% 1.43/1.64      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['43'])).
% 1.43/1.64  thf('45', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.64         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.43/1.64      inference('sup+', [status(thm)], ['42', '44'])).
% 1.43/1.64  thf('46', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.43/1.64  thf(zf_stmt_3, axiom,
% 1.43/1.64    (![C:$i,B:$i,A:$i]:
% 1.43/1.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.43/1.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.43/1.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.43/1.64  thf(zf_stmt_5, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i]:
% 1.43/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.43/1.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.43/1.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.43/1.64  thf('47', plain,
% 1.43/1.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.43/1.64         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.43/1.64          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.43/1.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.64  thf('48', plain,
% 1.43/1.64      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.43/1.64      inference('sup-', [status(thm)], ['46', '47'])).
% 1.43/1.64  thf('49', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.43/1.64          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.43/1.64      inference('sup-', [status(thm)], ['45', '48'])).
% 1.43/1.64  thf('50', plain,
% 1.43/1.64      (![X4 : $i, X5 : $i]:
% 1.43/1.64         (((X4) = (k1_xboole_0))
% 1.43/1.64          | ((X5) = (k1_xboole_0))
% 1.43/1.64          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.64  thf('51', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.43/1.64          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.43/1.64          | ((sk_B) = (k1_xboole_0))
% 1.43/1.64          | ((X0) = (k1_xboole_0)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['49', '50'])).
% 1.43/1.64  thf('52', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((X0) = (k1_xboole_0))
% 1.43/1.64          | ((sk_B) = (k1_xboole_0))
% 1.43/1.64          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.43/1.64      inference('simplify', [status(thm)], ['51'])).
% 1.43/1.64  thf('53', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('54', plain,
% 1.43/1.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.43/1.64      inference('split', [status(esa)], ['53'])).
% 1.43/1.64  thf('55', plain,
% 1.43/1.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('split', [status(esa)], ['53'])).
% 1.43/1.64  thf('56', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('57', plain,
% 1.43/1.64      (((m1_subset_1 @ sk_D @ 
% 1.43/1.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup+', [status(thm)], ['55', '56'])).
% 1.43/1.64  thf('58', plain,
% 1.43/1.64      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['43'])).
% 1.43/1.64  thf('59', plain,
% 1.43/1.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['57', '58'])).
% 1.43/1.64  thf('60', plain,
% 1.43/1.64      (![X5 : $i, X6 : $i]:
% 1.43/1.64         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.64  thf('61', plain,
% 1.43/1.64      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['60'])).
% 1.43/1.64  thf('62', plain,
% 1.43/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.43/1.64         ((v4_relat_1 @ X14 @ X15)
% 1.43/1.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.43/1.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.43/1.64  thf('63', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.64          | (v4_relat_1 @ X1 @ X0))),
% 1.43/1.64      inference('sup-', [status(thm)], ['61', '62'])).
% 1.43/1.64  thf('64', plain,
% 1.43/1.64      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['59', '63'])).
% 1.43/1.64  thf('65', plain,
% 1.43/1.64      (![X7 : $i, X8 : $i]:
% 1.43/1.64         (((X7) = (k7_relat_1 @ X7 @ X8))
% 1.43/1.64          | ~ (v4_relat_1 @ X7 @ X8)
% 1.43/1.64          | ~ (v1_relat_1 @ X7))),
% 1.43/1.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.43/1.64  thf('66', plain,
% 1.43/1.64      ((![X0 : $i]:
% 1.43/1.64          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['64', '65'])).
% 1.43/1.64  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 1.43/1.64      inference('sup-', [status(thm)], ['28', '29'])).
% 1.43/1.64  thf('68', plain,
% 1.43/1.64      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['66', '67'])).
% 1.43/1.64  thf('69', plain,
% 1.43/1.64      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 1.43/1.64        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 1.43/1.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 1.43/1.64      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 1.43/1.64  thf('70', plain,
% 1.43/1.64      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 1.43/1.64         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['68', '69'])).
% 1.43/1.64  thf('71', plain,
% 1.43/1.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('split', [status(esa)], ['53'])).
% 1.43/1.64  thf('72', plain, ((r1_tarski @ sk_C @ sk_A)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('73', plain,
% 1.43/1.64      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup+', [status(thm)], ['71', '72'])).
% 1.43/1.64  thf(t3_xboole_1, axiom,
% 1.43/1.64    (![A:$i]:
% 1.43/1.64     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.43/1.64  thf('74', plain,
% 1.43/1.64      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 1.43/1.64      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.43/1.64  thf('75', plain,
% 1.43/1.64      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['73', '74'])).
% 1.43/1.64  thf('76', plain,
% 1.43/1.64      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['43'])).
% 1.43/1.64  thf('77', plain,
% 1.43/1.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['57', '58'])).
% 1.43/1.64  thf('78', plain,
% 1.43/1.64      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['73', '74'])).
% 1.43/1.64  thf('79', plain,
% 1.43/1.64      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['66', '67'])).
% 1.43/1.64  thf('80', plain,
% 1.43/1.64      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['73', '74'])).
% 1.43/1.64  thf('81', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.43/1.64      inference('simplify', [status(thm)], ['16'])).
% 1.43/1.64  thf('82', plain,
% 1.43/1.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['57', '58'])).
% 1.43/1.64  thf('83', plain,
% 1.43/1.64      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['43'])).
% 1.43/1.64  thf('84', plain,
% 1.43/1.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.43/1.64         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.43/1.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.43/1.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.43/1.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.43/1.64  thf('85', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.64          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.43/1.64          | ~ (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 1.43/1.64      inference('sup-', [status(thm)], ['83', '84'])).
% 1.43/1.64  thf('86', plain,
% 1.43/1.64      ((![X0 : $i, X1 : $i]:
% 1.43/1.64          (~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 1.43/1.64           | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['82', '85'])).
% 1.43/1.64  thf('87', plain,
% 1.43/1.64      ((![X0 : $i]:
% 1.43/1.64          (m1_subset_1 @ sk_D @ 
% 1.43/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['81', '86'])).
% 1.43/1.64  thf(redefinition_k1_relset_1, axiom,
% 1.43/1.64    (![A:$i,B:$i,C:$i]:
% 1.43/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.43/1.64  thf('88', plain,
% 1.43/1.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.43/1.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.64  thf('89', plain,
% 1.43/1.64      ((![X0 : $i]:
% 1.43/1.64          ((k1_relset_1 @ (k1_relat_1 @ sk_D) @ X0 @ sk_D)
% 1.43/1.64            = (k1_relat_1 @ sk_D)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['87', '88'])).
% 1.43/1.64  thf('90', plain,
% 1.43/1.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.43/1.64         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 1.43/1.64          | (v1_funct_2 @ X28 @ X26 @ X27)
% 1.43/1.64          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.43/1.64  thf('91', plain,
% 1.43/1.64      ((![X0 : $i]:
% 1.43/1.64          (((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_D))
% 1.43/1.64           | ~ (zip_tseitin_1 @ sk_D @ X0 @ (k1_relat_1 @ sk_D))
% 1.43/1.64           | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ X0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['89', '90'])).
% 1.43/1.64  thf('92', plain,
% 1.43/1.64      ((![X0 : $i]:
% 1.43/1.64          ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ X0)
% 1.43/1.64           | ~ (zip_tseitin_1 @ sk_D @ X0 @ (k1_relat_1 @ sk_D))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('simplify', [status(thm)], ['91'])).
% 1.43/1.64  thf('93', plain,
% 1.43/1.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('split', [status(esa)], ['53'])).
% 1.43/1.64  thf('94', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('95', plain,
% 1.43/1.64      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup+', [status(thm)], ['93', '94'])).
% 1.43/1.64  thf('96', plain,
% 1.43/1.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.43/1.64         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.43/1.64          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.43/1.64          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.43/1.64  thf('97', plain,
% 1.43/1.64      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.43/1.64         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['95', '96'])).
% 1.43/1.64  thf('98', plain,
% 1.43/1.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['57', '58'])).
% 1.43/1.64  thf('99', plain,
% 1.43/1.64      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['43'])).
% 1.43/1.64  thf('100', plain,
% 1.43/1.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.43/1.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.64  thf('101', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.64          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['99', '100'])).
% 1.43/1.64  thf('102', plain,
% 1.43/1.64      ((![X0 : $i]:
% 1.43/1.64          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['98', '101'])).
% 1.43/1.64  thf('103', plain,
% 1.43/1.64      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 1.43/1.64         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['97', '102'])).
% 1.43/1.64  thf('104', plain,
% 1.43/1.64      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['57', '58'])).
% 1.43/1.64  thf('105', plain,
% 1.43/1.64      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.43/1.64      inference('simplify', [status(thm)], ['43'])).
% 1.43/1.64  thf('106', plain,
% 1.43/1.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.43/1.64         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.43/1.64          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.43/1.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.64  thf('107', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.64          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.43/1.64          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.43/1.64      inference('sup-', [status(thm)], ['105', '106'])).
% 1.43/1.64  thf('108', plain,
% 1.43/1.64      (![X24 : $i, X25 : $i]:
% 1.43/1.64         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.64  thf('109', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 1.43/1.64      inference('simplify', [status(thm)], ['108'])).
% 1.43/1.64  thf('110', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.64          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.43/1.64      inference('demod', [status(thm)], ['107', '109'])).
% 1.43/1.64  thf('111', plain,
% 1.43/1.64      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['104', '110'])).
% 1.43/1.64  thf('112', plain,
% 1.43/1.64      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['103', '111'])).
% 1.43/1.64  thf('113', plain,
% 1.43/1.64      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['103', '111'])).
% 1.43/1.64  thf('114', plain,
% 1.43/1.64      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['104', '110'])).
% 1.43/1.64  thf('115', plain,
% 1.43/1.64      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 1.43/1.64         <= ((((sk_A) = (k1_xboole_0))))),
% 1.43/1.64      inference('demod', [status(thm)], ['92', '112', '113', '114'])).
% 1.43/1.64  thf('116', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.43/1.64      inference('demod', [status(thm)],
% 1.43/1.64                ['70', '75', '76', '77', '78', '79', '80', '115'])).
% 1.43/1.64  thf('117', plain,
% 1.43/1.64      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.43/1.64      inference('split', [status(esa)], ['53'])).
% 1.43/1.64  thf('118', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.43/1.64      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 1.43/1.64  thf('119', plain, (((sk_B) != (k1_xboole_0))),
% 1.43/1.64      inference('simpl_trail', [status(thm)], ['54', '118'])).
% 1.43/1.64  thf('120', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((X0) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.43/1.64      inference('simplify_reflect-', [status(thm)], ['52', '119'])).
% 1.43/1.64  thf('121', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('122', plain,
% 1.43/1.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.43/1.64         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.43/1.64          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.43/1.64          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.43/1.64  thf('123', plain,
% 1.43/1.64      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.43/1.64        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['121', '122'])).
% 1.43/1.64  thf('124', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('125', plain,
% 1.43/1.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.43/1.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.64  thf('126', plain,
% 1.43/1.64      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.43/1.64      inference('sup-', [status(thm)], ['124', '125'])).
% 1.43/1.64  thf('127', plain,
% 1.43/1.64      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('demod', [status(thm)], ['123', '126'])).
% 1.43/1.64  thf('128', plain,
% 1.43/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['120', '127'])).
% 1.43/1.64  thf('129', plain,
% 1.43/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['120', '127'])).
% 1.43/1.64  thf('130', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         (((X1) = (X0))
% 1.43/1.64          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.43/1.64          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.64      inference('sup+', [status(thm)], ['128', '129'])).
% 1.43/1.64  thf('131', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 1.43/1.64      inference('simplify', [status(thm)], ['130'])).
% 1.43/1.64  thf('132', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.43/1.64      inference('condensation', [status(thm)], ['131'])).
% 1.43/1.64  thf('133', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))
% 1.43/1.64          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.43/1.64      inference('demod', [status(thm)], ['41', '132'])).
% 1.43/1.64  thf('134', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 1.43/1.64      inference('sup-', [status(thm)], ['18', '133'])).
% 1.43/1.64  thf('135', plain,
% 1.43/1.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('136', plain,
% 1.43/1.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.43/1.64         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.43/1.64          | ~ (v1_funct_1 @ X32)
% 1.43/1.64          | (m1_subset_1 @ (k2_partfun1 @ X33 @ X34 @ X32 @ X35) @ 
% 1.43/1.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.43/1.64      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 1.43/1.64  thf('137', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 1.43/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.43/1.64          | ~ (v1_funct_1 @ sk_D))),
% 1.43/1.64      inference('sup-', [status(thm)], ['135', '136'])).
% 1.43/1.64  thf('138', plain, ((v1_funct_1 @ sk_D)),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.64  thf('139', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 1.43/1.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('demod', [status(thm)], ['137', '138'])).
% 1.43/1.64  thf('140', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.43/1.64      inference('demod', [status(thm)], ['3', '4'])).
% 1.43/1.64  thf('141', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.43/1.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.43/1.64      inference('demod', [status(thm)], ['139', '140'])).
% 1.43/1.64  thf('142', plain,
% 1.43/1.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.43/1.64         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.43/1.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.43/1.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.43/1.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.43/1.64  thf('143', plain,
% 1.43/1.64      (![X0 : $i, X1 : $i]:
% 1.43/1.64         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.43/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.43/1.64          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 1.43/1.64      inference('sup-', [status(thm)], ['141', '142'])).
% 1.43/1.64  thf('144', plain,
% 1.43/1.64      (![X0 : $i]:
% 1.43/1.64         (~ (r1_tarski @ sk_C @ X0)
% 1.43/1.64          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 1.43/1.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 1.43/1.64      inference('sup-', [status(thm)], ['134', '143'])).
% 1.43/1.64  thf('145', plain,
% 1.43/1.64      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 1.43/1.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['17', '144'])).
% 1.43/1.64  thf('146', plain,
% 1.43/1.64      (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 1.43/1.64      inference('demod', [status(thm)], ['15', '145'])).
% 1.43/1.64  thf('147', plain,
% 1.43/1.64      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 1.43/1.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['17', '144'])).
% 1.43/1.64  thf('148', plain,
% 1.43/1.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.64         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.43/1.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.64  thf('149', plain,
% 1.43/1.64      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C))
% 1.43/1.64         = (k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['147', '148'])).
% 1.43/1.64  thf('150', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 1.43/1.64      inference('sup-', [status(thm)], ['18', '133'])).
% 1.43/1.64  thf('151', plain,
% 1.43/1.64      (((k1_relset_1 @ sk_C @ sk_B @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 1.43/1.64      inference('demod', [status(thm)], ['149', '150'])).
% 1.43/1.64  thf('152', plain,
% 1.43/1.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.43/1.64         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 1.43/1.64          | (v1_funct_2 @ X28 @ X26 @ X27)
% 1.43/1.64          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.43/1.64  thf('153', plain,
% 1.43/1.64      ((((sk_C) != (sk_C))
% 1.43/1.64        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 1.43/1.64        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 1.43/1.64      inference('sup-', [status(thm)], ['151', '152'])).
% 1.43/1.64  thf('154', plain,
% 1.43/1.64      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 1.43/1.64        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 1.43/1.64      inference('simplify', [status(thm)], ['153'])).
% 1.43/1.64  thf('155', plain,
% 1.43/1.64      (![X24 : $i, X25 : $i]:
% 1.43/1.64         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.64  thf('156', plain,
% 1.43/1.64      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 1.43/1.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.43/1.64      inference('sup-', [status(thm)], ['17', '144'])).
% 1.43/1.64  thf('157', plain,
% 1.43/1.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.43/1.64         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.43/1.64          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.43/1.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.43/1.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.64  thf('158', plain,
% 1.43/1.64      (((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)
% 1.43/1.64        | ~ (zip_tseitin_0 @ sk_B @ sk_C))),
% 1.43/1.64      inference('sup-', [status(thm)], ['156', '157'])).
% 1.43/1.64  thf('159', plain,
% 1.43/1.64      ((((sk_B) = (k1_xboole_0))
% 1.43/1.64        | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C))),
% 1.43/1.64      inference('sup-', [status(thm)], ['155', '158'])).
% 1.43/1.64  thf('160', plain, (((sk_B) != (k1_xboole_0))),
% 1.43/1.64      inference('simpl_trail', [status(thm)], ['54', '118'])).
% 1.43/1.64  thf('161', plain,
% 1.43/1.64      ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_B @ sk_C)),
% 1.43/1.64      inference('simplify_reflect-', [status(thm)], ['159', '160'])).
% 1.43/1.64  thf('162', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 1.43/1.64      inference('demod', [status(thm)], ['154', '161'])).
% 1.43/1.64  thf('163', plain, ($false), inference('demod', [status(thm)], ['146', '162'])).
% 1.43/1.64  
% 1.43/1.64  % SZS output end Refutation
% 1.43/1.64  
% 1.43/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
