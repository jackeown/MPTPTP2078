%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ys3ndadgvE

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:44 EST 2020

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  205 (1857 expanded)
%              Number of leaves         :   40 ( 532 expanded)
%              Depth                    :   30
%              Number of atoms          : 1579 (31882 expanded)
%              Number of equality atoms :  127 (2080 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) ) ) ),
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

thf('16',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['36','41'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','49'])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('60',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( v4_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( sk_D
          = ( k7_relat_1 @ sk_D @ X0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('69',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('71',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('74',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','57'])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','57'])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','57'])).

thf('87',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('97',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','97'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
          = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','103'])).

thf('105',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','57'])).

thf('109',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('110',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('113',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['111','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','115'])).

thf('117',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['69','74','75','76','77','78','79','116'])).

thf('118',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','119'])).

thf('121',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['50','120'])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','121'])).

thf('123',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','119'])).

thf('124',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','124'])).

thf('126',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('143',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['141','146'])).

thf('148',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('151',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('152',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['130','152'])).

thf('154',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','129'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['141','146'])).

thf('157',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('160',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['155','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['154','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ys3ndadgvE
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.61/2.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.61/2.81  % Solved by: fo/fo7.sh
% 2.61/2.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.61/2.81  % done 1237 iterations in 2.342s
% 2.61/2.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.61/2.81  % SZS output start Refutation
% 2.61/2.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.61/2.81  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.61/2.81  thf(sk_A_type, type, sk_A: $i).
% 2.61/2.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.61/2.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.61/2.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.61/2.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.61/2.81  thf(sk_D_type, type, sk_D: $i).
% 2.61/2.81  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.61/2.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.61/2.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.61/2.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.61/2.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.61/2.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.61/2.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.61/2.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.61/2.81  thf(sk_B_type, type, sk_B: $i).
% 2.61/2.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.61/2.81  thf(sk_C_type, type, sk_C: $i).
% 2.61/2.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.61/2.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.61/2.81  thf(t38_funct_2, conjecture,
% 2.61/2.81    (![A:$i,B:$i,C:$i,D:$i]:
% 2.61/2.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.61/2.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.61/2.81       ( ( r1_tarski @ C @ A ) =>
% 2.61/2.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.61/2.81           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 2.61/2.81             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 2.61/2.81             ( m1_subset_1 @
% 2.61/2.81               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 2.61/2.81               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 2.61/2.81  thf(zf_stmt_0, negated_conjecture,
% 2.61/2.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.61/2.81        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.61/2.81            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.61/2.81          ( ( r1_tarski @ C @ A ) =>
% 2.61/2.81            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.61/2.81              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 2.61/2.81                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 2.61/2.81                ( m1_subset_1 @
% 2.61/2.81                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 2.61/2.81                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 2.61/2.81    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 2.61/2.81  thf('0', plain,
% 2.61/2.81      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 2.61/2.81        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 2.61/2.81             sk_B)
% 2.61/2.81        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 2.61/2.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('1', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(redefinition_k2_partfun1, axiom,
% 2.61/2.81    (![A:$i,B:$i,C:$i,D:$i]:
% 2.61/2.81     ( ( ( v1_funct_1 @ C ) & 
% 2.61/2.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.61/2.81       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 2.61/2.81  thf('2', plain,
% 2.61/2.81      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.61/2.81          | ~ (v1_funct_1 @ X32)
% 2.61/2.81          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 2.61/2.81      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 2.61/2.81  thf('3', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 2.61/2.81          | ~ (v1_funct_1 @ sk_D))),
% 2.61/2.81      inference('sup-', [status(thm)], ['1', '2'])).
% 2.61/2.81  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('5', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['3', '4'])).
% 2.61/2.81  thf('6', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(dt_k2_partfun1, axiom,
% 2.61/2.81    (![A:$i,B:$i,C:$i,D:$i]:
% 2.61/2.81     ( ( ( v1_funct_1 @ C ) & 
% 2.61/2.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.61/2.81       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 2.61/2.81         ( m1_subset_1 @
% 2.61/2.81           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 2.61/2.81           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.61/2.81  thf('7', plain,
% 2.61/2.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.61/2.81          | ~ (v1_funct_1 @ X28)
% 2.61/2.81          | (v1_funct_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31)))),
% 2.61/2.81      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 2.61/2.81  thf('8', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 2.61/2.81          | ~ (v1_funct_1 @ sk_D))),
% 2.61/2.81      inference('sup-', [status(thm)], ['6', '7'])).
% 2.61/2.81  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('10', plain,
% 2.61/2.81      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['8', '9'])).
% 2.61/2.81  thf('11', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['3', '4'])).
% 2.61/2.81  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['10', '11'])).
% 2.61/2.81  thf('13', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['3', '4'])).
% 2.61/2.81  thf('14', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['3', '4'])).
% 2.61/2.81  thf('15', plain,
% 2.61/2.81      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 2.61/2.81        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.61/2.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 2.61/2.81      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 2.61/2.81  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(d1_funct_2, axiom,
% 2.61/2.81    (![A:$i,B:$i,C:$i]:
% 2.61/2.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.61/2.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.61/2.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.61/2.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.61/2.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.61/2.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.61/2.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.61/2.81  thf(zf_stmt_1, axiom,
% 2.61/2.81    (![C:$i,B:$i,A:$i]:
% 2.61/2.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.61/2.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.61/2.81  thf('18', plain,
% 2.61/2.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.61/2.81         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 2.61/2.81          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 2.61/2.81          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.61/2.81  thf('19', plain,
% 2.61/2.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 2.61/2.81        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['17', '18'])).
% 2.61/2.81  thf('20', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(redefinition_k1_relset_1, axiom,
% 2.61/2.81    (![A:$i,B:$i,C:$i]:
% 2.61/2.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.61/2.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.61/2.81  thf('21', plain,
% 2.61/2.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.61/2.81         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 2.61/2.81          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.61/2.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.61/2.81  thf('22', plain,
% 2.61/2.81      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.61/2.81      inference('sup-', [status(thm)], ['20', '21'])).
% 2.61/2.81  thf('23', plain,
% 2.61/2.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.61/2.81      inference('demod', [status(thm)], ['19', '22'])).
% 2.61/2.81  thf(zf_stmt_2, axiom,
% 2.61/2.81    (![B:$i,A:$i]:
% 2.61/2.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.61/2.81       ( zip_tseitin_0 @ B @ A ) ))).
% 2.61/2.81  thf('24', plain,
% 2.61/2.81      (![X20 : $i, X21 : $i]:
% 2.61/2.81         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.61/2.81  thf('25', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.61/2.81  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.61/2.81  thf(zf_stmt_5, axiom,
% 2.61/2.81    (![A:$i,B:$i,C:$i]:
% 2.61/2.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.61/2.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.61/2.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.61/2.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.61/2.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.61/2.81  thf('26', plain,
% 2.61/2.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.61/2.81         (~ (zip_tseitin_0 @ X25 @ X26)
% 2.61/2.81          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 2.61/2.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.61/2.81  thf('27', plain,
% 2.61/2.81      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.61/2.81      inference('sup-', [status(thm)], ['25', '26'])).
% 2.61/2.81  thf('28', plain,
% 2.61/2.81      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 2.61/2.81      inference('sup-', [status(thm)], ['24', '27'])).
% 2.61/2.81  thf('29', plain,
% 2.61/2.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.61/2.81      inference('demod', [status(thm)], ['19', '22'])).
% 2.61/2.81  thf('30', plain,
% 2.61/2.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['28', '29'])).
% 2.61/2.81  thf('31', plain,
% 2.61/2.81      (![X20 : $i, X21 : $i]:
% 2.61/2.81         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.61/2.81  thf('32', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(cc2_relset_1, axiom,
% 2.61/2.81    (![A:$i,B:$i,C:$i]:
% 2.61/2.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.61/2.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.61/2.81  thf('33', plain,
% 2.61/2.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.61/2.81         ((v5_relat_1 @ X14 @ X16)
% 2.61/2.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.61/2.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.61/2.81  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 2.61/2.81      inference('sup-', [status(thm)], ['32', '33'])).
% 2.61/2.81  thf(d19_relat_1, axiom,
% 2.61/2.81    (![A:$i,B:$i]:
% 2.61/2.81     ( ( v1_relat_1 @ B ) =>
% 2.61/2.81       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.61/2.81  thf('35', plain,
% 2.61/2.81      (![X6 : $i, X7 : $i]:
% 2.61/2.81         (~ (v5_relat_1 @ X6 @ X7)
% 2.61/2.81          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 2.61/2.81          | ~ (v1_relat_1 @ X6))),
% 2.61/2.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.61/2.81  thf('36', plain,
% 2.61/2.81      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 2.61/2.81      inference('sup-', [status(thm)], ['34', '35'])).
% 2.61/2.81  thf('37', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf(cc2_relat_1, axiom,
% 2.61/2.81    (![A:$i]:
% 2.61/2.81     ( ( v1_relat_1 @ A ) =>
% 2.61/2.81       ( ![B:$i]:
% 2.61/2.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.61/2.81  thf('38', plain,
% 2.61/2.81      (![X4 : $i, X5 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.61/2.81          | (v1_relat_1 @ X4)
% 2.61/2.81          | ~ (v1_relat_1 @ X5))),
% 2.61/2.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.61/2.81  thf('39', plain,
% 2.61/2.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 2.61/2.81      inference('sup-', [status(thm)], ['37', '38'])).
% 2.61/2.81  thf(fc6_relat_1, axiom,
% 2.61/2.81    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.61/2.81  thf('40', plain,
% 2.61/2.81      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.61/2.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.61/2.81  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 2.61/2.81      inference('demod', [status(thm)], ['39', '40'])).
% 2.61/2.81  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.61/2.81      inference('demod', [status(thm)], ['36', '41'])).
% 2.61/2.81  thf(t4_funct_2, axiom,
% 2.61/2.81    (![A:$i,B:$i]:
% 2.61/2.81     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.61/2.81       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.61/2.81         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 2.61/2.81           ( m1_subset_1 @
% 2.61/2.81             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 2.61/2.81  thf('43', plain,
% 2.61/2.81      (![X36 : $i, X37 : $i]:
% 2.61/2.81         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 2.61/2.81          | (m1_subset_1 @ X36 @ 
% 2.61/2.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 2.61/2.81          | ~ (v1_funct_1 @ X36)
% 2.61/2.81          | ~ (v1_relat_1 @ X36))),
% 2.61/2.81      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.61/2.81  thf('44', plain,
% 2.61/2.81      ((~ (v1_relat_1 @ sk_D)
% 2.61/2.81        | ~ (v1_funct_1 @ sk_D)
% 2.61/2.81        | (m1_subset_1 @ sk_D @ 
% 2.61/2.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['42', '43'])).
% 2.61/2.81  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 2.61/2.81      inference('demod', [status(thm)], ['39', '40'])).
% 2.61/2.81  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('47', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ 
% 2.61/2.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 2.61/2.81      inference('demod', [status(thm)], ['44', '45', '46'])).
% 2.61/2.81  thf('48', plain,
% 2.61/2.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.61/2.81         (~ (zip_tseitin_0 @ X25 @ X26)
% 2.61/2.81          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 2.61/2.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.61/2.81  thf('49', plain,
% 2.61/2.81      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))
% 2.61/2.81        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_D)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['47', '48'])).
% 2.61/2.81  thf('50', plain,
% 2.61/2.81      ((((sk_B) = (k1_xboole_0))
% 2.61/2.81        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['31', '49'])).
% 2.61/2.81  thf('51', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('52', plain,
% 2.61/2.81      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.61/2.81      inference('split', [status(esa)], ['51'])).
% 2.61/2.81  thf('53', plain,
% 2.61/2.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('split', [status(esa)], ['51'])).
% 2.61/2.81  thf('54', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('55', plain,
% 2.61/2.81      (((m1_subset_1 @ sk_D @ 
% 2.61/2.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup+', [status(thm)], ['53', '54'])).
% 2.61/2.81  thf(t113_zfmisc_1, axiom,
% 2.61/2.81    (![A:$i,B:$i]:
% 2.61/2.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.61/2.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.61/2.81  thf('56', plain,
% 2.61/2.81      (![X2 : $i, X3 : $i]:
% 2.61/2.81         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 2.61/2.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.61/2.81  thf('57', plain,
% 2.61/2.81      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.61/2.81      inference('simplify', [status(thm)], ['56'])).
% 2.61/2.81  thf('58', plain,
% 2.61/2.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['55', '57'])).
% 2.61/2.81  thf('59', plain,
% 2.61/2.81      (![X2 : $i, X3 : $i]:
% 2.61/2.81         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.61/2.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.61/2.81  thf('60', plain,
% 2.61/2.81      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.61/2.81      inference('simplify', [status(thm)], ['59'])).
% 2.61/2.81  thf('61', plain,
% 2.61/2.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.61/2.81         ((v4_relat_1 @ X14 @ X15)
% 2.61/2.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.61/2.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.61/2.81  thf('62', plain,
% 2.61/2.81      (![X0 : $i, X1 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.61/2.81          | (v4_relat_1 @ X1 @ X0))),
% 2.61/2.81      inference('sup-', [status(thm)], ['60', '61'])).
% 2.61/2.81  thf('63', plain,
% 2.61/2.81      ((![X0 : $i]: (v4_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['58', '62'])).
% 2.61/2.81  thf(t209_relat_1, axiom,
% 2.61/2.81    (![A:$i,B:$i]:
% 2.61/2.81     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.61/2.81       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.61/2.81  thf('64', plain,
% 2.61/2.81      (![X10 : $i, X11 : $i]:
% 2.61/2.81         (((X10) = (k7_relat_1 @ X10 @ X11))
% 2.61/2.81          | ~ (v4_relat_1 @ X10 @ X11)
% 2.61/2.81          | ~ (v1_relat_1 @ X10))),
% 2.61/2.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.61/2.81  thf('65', plain,
% 2.61/2.81      ((![X0 : $i]:
% 2.61/2.81          (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0))))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['63', '64'])).
% 2.61/2.81  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 2.61/2.81      inference('demod', [status(thm)], ['39', '40'])).
% 2.61/2.81  thf('67', plain,
% 2.61/2.81      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['65', '66'])).
% 2.61/2.81  thf('68', plain,
% 2.61/2.81      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 2.61/2.81        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.61/2.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 2.61/2.81      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 2.61/2.81  thf('69', plain,
% 2.61/2.81      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 2.61/2.81         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['67', '68'])).
% 2.61/2.81  thf('70', plain,
% 2.61/2.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('split', [status(esa)], ['51'])).
% 2.61/2.81  thf('71', plain, ((r1_tarski @ sk_C @ sk_A)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('72', plain,
% 2.61/2.81      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup+', [status(thm)], ['70', '71'])).
% 2.61/2.81  thf(t3_xboole_1, axiom,
% 2.61/2.81    (![A:$i]:
% 2.61/2.81     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.61/2.81  thf('73', plain,
% 2.61/2.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.61/2.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.61/2.81  thf('74', plain,
% 2.61/2.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['72', '73'])).
% 2.61/2.81  thf('75', plain,
% 2.61/2.81      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.61/2.81      inference('simplify', [status(thm)], ['56'])).
% 2.61/2.81  thf('76', plain,
% 2.61/2.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['55', '57'])).
% 2.61/2.81  thf('77', plain,
% 2.61/2.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['72', '73'])).
% 2.61/2.81  thf('78', plain,
% 2.61/2.81      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['65', '66'])).
% 2.61/2.81  thf('79', plain,
% 2.61/2.81      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['72', '73'])).
% 2.61/2.81  thf('80', plain,
% 2.61/2.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['55', '57'])).
% 2.61/2.81  thf('81', plain,
% 2.61/2.81      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.61/2.81      inference('simplify', [status(thm)], ['56'])).
% 2.61/2.81  thf('82', plain,
% 2.61/2.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.61/2.81         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 2.61/2.81          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.61/2.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.61/2.81  thf('83', plain,
% 2.61/2.81      (![X0 : $i, X1 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.61/2.81          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['81', '82'])).
% 2.61/2.81  thf('84', plain,
% 2.61/2.81      ((![X0 : $i]:
% 2.61/2.81          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['80', '83'])).
% 2.61/2.81  thf('85', plain,
% 2.61/2.81      ((![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['65', '66'])).
% 2.61/2.81  thf('86', plain,
% 2.61/2.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['55', '57'])).
% 2.61/2.81  thf('87', plain,
% 2.61/2.81      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.61/2.81      inference('simplify', [status(thm)], ['56'])).
% 2.61/2.81  thf('88', plain,
% 2.61/2.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.61/2.81         ((v5_relat_1 @ X14 @ X16)
% 2.61/2.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.61/2.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.61/2.81  thf('89', plain,
% 2.61/2.81      (![X0 : $i, X1 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.61/2.81          | (v5_relat_1 @ X1 @ X0))),
% 2.61/2.81      inference('sup-', [status(thm)], ['87', '88'])).
% 2.61/2.81  thf('90', plain,
% 2.61/2.81      ((![X0 : $i]: (v5_relat_1 @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['86', '89'])).
% 2.61/2.81  thf('91', plain,
% 2.61/2.81      (![X6 : $i, X7 : $i]:
% 2.61/2.81         (~ (v5_relat_1 @ X6 @ X7)
% 2.61/2.81          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 2.61/2.81          | ~ (v1_relat_1 @ X6))),
% 2.61/2.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.61/2.81  thf('92', plain,
% 2.61/2.81      ((![X0 : $i]:
% 2.61/2.81          (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['90', '91'])).
% 2.61/2.81  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 2.61/2.81      inference('demod', [status(thm)], ['39', '40'])).
% 2.61/2.81  thf('94', plain,
% 2.61/2.81      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['92', '93'])).
% 2.61/2.81  thf('95', plain,
% 2.61/2.81      ((![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['92', '93'])).
% 2.61/2.81  thf('96', plain,
% 2.61/2.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.61/2.81      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.61/2.81  thf('97', plain,
% 2.61/2.81      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['95', '96'])).
% 2.61/2.81  thf('98', plain,
% 2.61/2.81      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['94', '97'])).
% 2.61/2.81  thf(t91_relat_1, axiom,
% 2.61/2.81    (![A:$i,B:$i]:
% 2.61/2.81     ( ( v1_relat_1 @ B ) =>
% 2.61/2.81       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.61/2.81         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.61/2.81  thf('99', plain,
% 2.61/2.81      (![X12 : $i, X13 : $i]:
% 2.61/2.81         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 2.61/2.81          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 2.61/2.81          | ~ (v1_relat_1 @ X13))),
% 2.61/2.81      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.61/2.81  thf('100', plain,
% 2.61/2.81      ((![X0 : $i]:
% 2.61/2.81          (~ (v1_relat_1 @ X0)
% 2.61/2.81           | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['98', '99'])).
% 2.61/2.81  thf('101', plain,
% 2.61/2.81      (((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup+', [status(thm)], ['85', '100'])).
% 2.61/2.81  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 2.61/2.81      inference('demod', [status(thm)], ['39', '40'])).
% 2.61/2.81  thf('103', plain,
% 2.61/2.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['101', '102'])).
% 2.61/2.81  thf('104', plain,
% 2.61/2.81      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['84', '103'])).
% 2.61/2.81  thf('105', plain,
% 2.61/2.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.61/2.81         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 2.61/2.81          | (v1_funct_2 @ X24 @ X22 @ X23)
% 2.61/2.81          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.61/2.81  thf('106', plain,
% 2.61/2.81      ((![X0 : $i]:
% 2.61/2.81          (((k1_xboole_0) != (k1_xboole_0))
% 2.61/2.81           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 2.61/2.81           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['104', '105'])).
% 2.61/2.81  thf('107', plain,
% 2.61/2.81      ((![X0 : $i]:
% 2.61/2.81          ((v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)
% 2.61/2.81           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('simplify', [status(thm)], ['106'])).
% 2.61/2.81  thf('108', plain,
% 2.61/2.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['55', '57'])).
% 2.61/2.81  thf('109', plain,
% 2.61/2.81      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 2.61/2.81      inference('simplify', [status(thm)], ['56'])).
% 2.61/2.81  thf('110', plain,
% 2.61/2.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.61/2.81         (~ (zip_tseitin_0 @ X25 @ X26)
% 2.61/2.81          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 2.61/2.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.61/2.81  thf('111', plain,
% 2.61/2.81      (![X0 : $i, X1 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.61/2.81          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 2.61/2.81          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 2.61/2.81      inference('sup-', [status(thm)], ['109', '110'])).
% 2.61/2.81  thf('112', plain,
% 2.61/2.81      (![X20 : $i, X21 : $i]:
% 2.61/2.81         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.61/2.81  thf('113', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 2.61/2.81      inference('simplify', [status(thm)], ['112'])).
% 2.61/2.81  thf('114', plain,
% 2.61/2.81      (![X0 : $i, X1 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.61/2.81          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 2.61/2.81      inference('demod', [status(thm)], ['111', '113'])).
% 2.61/2.81  thf('115', plain,
% 2.61/2.81      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['108', '114'])).
% 2.61/2.81  thf('116', plain,
% 2.61/2.81      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 2.61/2.81         <= ((((sk_A) = (k1_xboole_0))))),
% 2.61/2.81      inference('demod', [status(thm)], ['107', '115'])).
% 2.61/2.81  thf('117', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 2.61/2.81      inference('demod', [status(thm)],
% 2.61/2.81                ['69', '74', '75', '76', '77', '78', '79', '116'])).
% 2.61/2.81  thf('118', plain,
% 2.61/2.81      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.61/2.81      inference('split', [status(esa)], ['51'])).
% 2.61/2.81  thf('119', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 2.61/2.81      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 2.61/2.81  thf('120', plain, (((sk_B) != (k1_xboole_0))),
% 2.61/2.81      inference('simpl_trail', [status(thm)], ['52', '119'])).
% 2.61/2.81  thf('121', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_relat_1 @ sk_D))),
% 2.61/2.81      inference('simplify_reflect-', [status(thm)], ['50', '120'])).
% 2.61/2.81  thf('122', plain,
% 2.61/2.81      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 2.61/2.81      inference('sup+', [status(thm)], ['30', '121'])).
% 2.61/2.81  thf('123', plain, (((sk_B) != (k1_xboole_0))),
% 2.61/2.81      inference('simpl_trail', [status(thm)], ['52', '119'])).
% 2.61/2.81  thf('124', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 2.61/2.81      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 2.61/2.81  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.61/2.81      inference('demod', [status(thm)], ['23', '124'])).
% 2.61/2.81  thf('126', plain,
% 2.61/2.81      (![X12 : $i, X13 : $i]:
% 2.61/2.81         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 2.61/2.81          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 2.61/2.81          | ~ (v1_relat_1 @ X13))),
% 2.61/2.81      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.61/2.81  thf('127', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (~ (r1_tarski @ X0 @ sk_A)
% 2.61/2.81          | ~ (v1_relat_1 @ sk_D)
% 2.61/2.81          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['125', '126'])).
% 2.61/2.81  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 2.61/2.81      inference('demod', [status(thm)], ['39', '40'])).
% 2.61/2.81  thf('129', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (~ (r1_tarski @ X0 @ sk_A)
% 2.61/2.81          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 2.61/2.81      inference('demod', [status(thm)], ['127', '128'])).
% 2.61/2.81  thf('130', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 2.61/2.81      inference('sup-', [status(thm)], ['16', '129'])).
% 2.61/2.81  thf('131', plain,
% 2.61/2.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('132', plain,
% 2.61/2.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.61/2.81          | ~ (v1_funct_1 @ X28)
% 2.61/2.81          | (m1_subset_1 @ (k2_partfun1 @ X29 @ X30 @ X28 @ X31) @ 
% 2.61/2.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.61/2.81      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 2.61/2.81  thf('133', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 2.61/2.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.61/2.81          | ~ (v1_funct_1 @ sk_D))),
% 2.61/2.81      inference('sup-', [status(thm)], ['131', '132'])).
% 2.61/2.81  thf('134', plain, ((v1_funct_1 @ sk_D)),
% 2.61/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.61/2.81  thf('135', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 2.61/2.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('demod', [status(thm)], ['133', '134'])).
% 2.61/2.81  thf('136', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['3', '4'])).
% 2.61/2.81  thf('137', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.61/2.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('demod', [status(thm)], ['135', '136'])).
% 2.61/2.81  thf('138', plain,
% 2.61/2.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.61/2.81         ((v5_relat_1 @ X14 @ X16)
% 2.61/2.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.61/2.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.61/2.81  thf('139', plain,
% 2.61/2.81      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 2.61/2.81      inference('sup-', [status(thm)], ['137', '138'])).
% 2.61/2.81  thf('140', plain,
% 2.61/2.81      (![X6 : $i, X7 : $i]:
% 2.61/2.81         (~ (v5_relat_1 @ X6 @ X7)
% 2.61/2.81          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 2.61/2.81          | ~ (v1_relat_1 @ X6))),
% 2.61/2.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.61/2.81  thf('141', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 2.61/2.81          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 2.61/2.81      inference('sup-', [status(thm)], ['139', '140'])).
% 2.61/2.81  thf('142', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.61/2.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.61/2.81      inference('demod', [status(thm)], ['135', '136'])).
% 2.61/2.81  thf('143', plain,
% 2.61/2.81      (![X4 : $i, X5 : $i]:
% 2.61/2.81         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.61/2.81          | (v1_relat_1 @ X4)
% 2.61/2.81          | ~ (v1_relat_1 @ X5))),
% 2.61/2.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.61/2.81  thf('144', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.61/2.81          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 2.61/2.81      inference('sup-', [status(thm)], ['142', '143'])).
% 2.61/2.81  thf('145', plain,
% 2.61/2.81      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.61/2.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.61/2.81  thf('146', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['144', '145'])).
% 2.61/2.81  thf('147', plain,
% 2.61/2.81      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 2.61/2.81      inference('demod', [status(thm)], ['141', '146'])).
% 2.61/2.81  thf('148', plain,
% 2.61/2.81      (![X36 : $i, X37 : $i]:
% 2.61/2.81         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 2.61/2.81          | (v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ X37)
% 2.61/2.81          | ~ (v1_funct_1 @ X36)
% 2.61/2.81          | ~ (v1_relat_1 @ X36))),
% 2.61/2.81      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.61/2.81  thf('149', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 2.61/2.81          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 2.61/2.81          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.61/2.81             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 2.61/2.81      inference('sup-', [status(thm)], ['147', '148'])).
% 2.61/2.81  thf('150', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['144', '145'])).
% 2.61/2.81  thf('151', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['10', '11'])).
% 2.61/2.81  thf('152', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.61/2.81          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 2.61/2.81      inference('demod', [status(thm)], ['149', '150', '151'])).
% 2.61/2.81  thf('153', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 2.61/2.81      inference('sup+', [status(thm)], ['130', '152'])).
% 2.61/2.81  thf('154', plain,
% 2.61/2.81      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.61/2.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.61/2.81      inference('demod', [status(thm)], ['15', '153'])).
% 2.61/2.81  thf('155', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 2.61/2.81      inference('sup-', [status(thm)], ['16', '129'])).
% 2.61/2.81  thf('156', plain,
% 2.61/2.81      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 2.61/2.81      inference('demod', [status(thm)], ['141', '146'])).
% 2.61/2.81  thf('157', plain,
% 2.61/2.81      (![X36 : $i, X37 : $i]:
% 2.61/2.81         (~ (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 2.61/2.81          | (m1_subset_1 @ X36 @ 
% 2.61/2.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 2.61/2.81          | ~ (v1_funct_1 @ X36)
% 2.61/2.81          | ~ (v1_relat_1 @ X36))),
% 2.61/2.81      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.61/2.81  thf('158', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 2.61/2.81          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 2.61/2.81          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.61/2.81             (k1_zfmisc_1 @ 
% 2.61/2.81              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 2.61/2.81      inference('sup-', [status(thm)], ['156', '157'])).
% 2.61/2.81  thf('159', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['144', '145'])).
% 2.61/2.81  thf('160', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 2.61/2.81      inference('demod', [status(thm)], ['10', '11'])).
% 2.61/2.81  thf('161', plain,
% 2.61/2.81      (![X0 : $i]:
% 2.61/2.81         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.61/2.81          (k1_zfmisc_1 @ 
% 2.61/2.81           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 2.61/2.81      inference('demod', [status(thm)], ['158', '159', '160'])).
% 2.61/2.81  thf('162', plain,
% 2.61/2.81      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 2.61/2.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.61/2.81      inference('sup+', [status(thm)], ['155', '161'])).
% 2.61/2.81  thf('163', plain, ($false), inference('demod', [status(thm)], ['154', '162'])).
% 2.61/2.81  
% 2.61/2.81  % SZS output end Refutation
% 2.61/2.81  
% 2.61/2.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
