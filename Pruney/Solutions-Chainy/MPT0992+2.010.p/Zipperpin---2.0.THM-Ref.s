%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L6GdonlJ3S

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:36 EST 2020

% Result     : Theorem 3.42s
% Output     : Refutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  190 (1733 expanded)
%              Number of leaves         :   39 ( 558 expanded)
%              Depth                    :   23
%              Number of atoms          : 1462 (21538 expanded)
%              Number of equality atoms :  114 (1082 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) ) ) ),
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

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ( X30 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('53',plain,(
    ! [X29: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X1 @ X3 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','69'])).

thf('71',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('80',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('81',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('85',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('92',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('99',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('100',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('101',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('103',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['85','96','97','98','99','100','101','104'])).

thf('106',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['72','107'])).

thf('109',plain,(
    ! [X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','108'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('111',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('113',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('128',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('131',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['129','132'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('134',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ X40 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['118','138'])).

thf('140',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','117'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['129','132'])).

thf('143',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('146',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['140','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L6GdonlJ3S
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:06:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.42/3.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.42/3.61  % Solved by: fo/fo7.sh
% 3.42/3.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.42/3.61  % done 3635 iterations in 3.151s
% 3.42/3.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.42/3.61  % SZS output start Refutation
% 3.42/3.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.42/3.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.42/3.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.42/3.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.42/3.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.42/3.61  thf(sk_D_type, type, sk_D: $i).
% 3.42/3.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.42/3.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.42/3.61  thf(sk_C_type, type, sk_C: $i).
% 3.42/3.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.42/3.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.42/3.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.42/3.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.42/3.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.42/3.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.42/3.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.42/3.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.42/3.61  thf(sk_B_type, type, sk_B: $i).
% 3.42/3.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.42/3.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.42/3.61  thf(sk_A_type, type, sk_A: $i).
% 3.42/3.61  thf(t38_funct_2, conjecture,
% 3.42/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.42/3.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.42/3.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.42/3.61       ( ( r1_tarski @ C @ A ) =>
% 3.42/3.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.42/3.61           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 3.42/3.61             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 3.42/3.61             ( m1_subset_1 @
% 3.42/3.61               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 3.42/3.61               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 3.42/3.61  thf(zf_stmt_0, negated_conjecture,
% 3.42/3.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.42/3.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.42/3.61            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.42/3.61          ( ( r1_tarski @ C @ A ) =>
% 3.42/3.61            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.42/3.61              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 3.42/3.61                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 3.42/3.61                ( m1_subset_1 @
% 3.42/3.61                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 3.42/3.61                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 3.42/3.61    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 3.42/3.61  thf('0', plain,
% 3.42/3.61      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 3.42/3.61        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 3.42/3.61             sk_B)
% 3.42/3.61        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 3.42/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('1', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf(redefinition_k2_partfun1, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.42/3.61     ( ( ( v1_funct_1 @ C ) & 
% 3.42/3.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.42/3.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 3.42/3.61  thf('2', plain,
% 3.42/3.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.42/3.61         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.42/3.61          | ~ (v1_funct_1 @ X35)
% 3.42/3.61          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 3.42/3.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 3.42/3.61  thf('3', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 3.42/3.61          | ~ (v1_funct_1 @ sk_D))),
% 3.42/3.61      inference('sup-', [status(thm)], ['1', '2'])).
% 3.42/3.61  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('5', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['3', '4'])).
% 3.42/3.61  thf('6', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf(dt_k2_partfun1, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i,D:$i]:
% 3.42/3.61     ( ( ( v1_funct_1 @ C ) & 
% 3.42/3.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.42/3.61       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 3.42/3.61         ( m1_subset_1 @
% 3.42/3.61           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 3.42/3.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.42/3.61  thf('7', plain,
% 3.42/3.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.42/3.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.42/3.61          | ~ (v1_funct_1 @ X31)
% 3.42/3.61          | (v1_funct_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34)))),
% 3.42/3.61      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.42/3.61  thf('8', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 3.42/3.61          | ~ (v1_funct_1 @ sk_D))),
% 3.42/3.61      inference('sup-', [status(thm)], ['6', '7'])).
% 3.42/3.61  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('10', plain,
% 3.42/3.61      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['8', '9'])).
% 3.42/3.61  thf('11', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['3', '4'])).
% 3.42/3.61  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['10', '11'])).
% 3.42/3.61  thf('13', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['3', '4'])).
% 3.42/3.61  thf('14', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['3', '4'])).
% 3.42/3.61  thf('15', plain,
% 3.42/3.61      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 3.42/3.61        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.42/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.42/3.61      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.42/3.61  thf('16', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf(d1_funct_2, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i]:
% 3.42/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.42/3.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.42/3.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.42/3.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.42/3.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.42/3.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.42/3.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.42/3.61  thf(zf_stmt_1, axiom,
% 3.42/3.61    (![B:$i,A:$i]:
% 3.42/3.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.42/3.61       ( zip_tseitin_0 @ B @ A ) ))).
% 3.42/3.61  thf('17', plain,
% 3.42/3.61      (![X23 : $i, X24 : $i]:
% 3.42/3.61         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.42/3.61  thf('18', plain,
% 3.42/3.61      (![X23 : $i, X24 : $i]:
% 3.42/3.61         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.42/3.61  thf('19', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 3.42/3.61      inference('simplify', [status(thm)], ['18'])).
% 3.42/3.61  thf('20', plain,
% 3.42/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.42/3.61         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.42/3.61      inference('sup+', [status(thm)], ['17', '19'])).
% 3.42/3.61  thf('21', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.42/3.61  thf(zf_stmt_3, axiom,
% 3.42/3.61    (![C:$i,B:$i,A:$i]:
% 3.42/3.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.42/3.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.42/3.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.42/3.61  thf(zf_stmt_5, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i]:
% 3.42/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.42/3.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.42/3.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.42/3.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.42/3.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.42/3.61  thf('22', plain,
% 3.42/3.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.42/3.61         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.42/3.61          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.42/3.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.42/3.61  thf('23', plain,
% 3.42/3.61      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.42/3.61      inference('sup-', [status(thm)], ['21', '22'])).
% 3.42/3.61  thf('24', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((zip_tseitin_0 @ X0 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.42/3.61      inference('sup-', [status(thm)], ['20', '23'])).
% 3.42/3.61  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('26', plain,
% 3.42/3.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.42/3.61         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 3.42/3.61          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 3.42/3.61          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.42/3.61  thf('27', plain,
% 3.42/3.61      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.42/3.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['25', '26'])).
% 3.42/3.61  thf('28', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf(redefinition_k1_relset_1, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i]:
% 3.42/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.42/3.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.42/3.61  thf('29', plain,
% 3.42/3.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.42/3.61         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 3.42/3.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.42/3.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.42/3.61  thf('30', plain,
% 3.42/3.61      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.42/3.61      inference('sup-', [status(thm)], ['28', '29'])).
% 3.42/3.61  thf('31', plain,
% 3.42/3.61      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.42/3.61      inference('demod', [status(thm)], ['27', '30'])).
% 3.42/3.61  thf('32', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((zip_tseitin_0 @ X0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['24', '31'])).
% 3.42/3.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.42/3.61  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.42/3.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.61  thf(t3_subset, axiom,
% 3.42/3.61    (![A:$i,B:$i]:
% 3.42/3.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.42/3.61  thf('34', plain,
% 3.42/3.61      (![X1 : $i, X3 : $i]:
% 3.42/3.61         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 3.42/3.61      inference('cnf', [status(esa)], [t3_subset])).
% 3.42/3.61  thf('35', plain,
% 3.42/3.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['33', '34'])).
% 3.42/3.61  thf('36', plain,
% 3.42/3.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.42/3.61         (~ (zip_tseitin_0 @ X28 @ X29)
% 3.42/3.61          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 3.42/3.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.42/3.61  thf('37', plain,
% 3.42/3.61      (![X0 : $i, X1 : $i]:
% 3.42/3.61         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.42/3.61      inference('sup-', [status(thm)], ['35', '36'])).
% 3.42/3.61  thf('38', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.42/3.61          | (zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_B))),
% 3.42/3.61      inference('sup-', [status(thm)], ['32', '37'])).
% 3.42/3.61  thf('39', plain,
% 3.42/3.61      (![X23 : $i, X24 : $i]:
% 3.42/3.61         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.42/3.61  thf('40', plain,
% 3.42/3.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['33', '34'])).
% 3.42/3.61  thf(cc2_relset_1, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i]:
% 3.42/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.42/3.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.42/3.61  thf('41', plain,
% 3.42/3.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.42/3.61         ((v4_relat_1 @ X17 @ X18)
% 3.42/3.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.42/3.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.42/3.61  thf('42', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 3.42/3.61      inference('sup-', [status(thm)], ['40', '41'])).
% 3.42/3.61  thf(t209_relat_1, axiom,
% 3.42/3.61    (![A:$i,B:$i]:
% 3.42/3.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.42/3.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.42/3.61  thf('43', plain,
% 3.42/3.61      (![X8 : $i, X9 : $i]:
% 3.42/3.61         (((X8) = (k7_relat_1 @ X8 @ X9))
% 3.42/3.61          | ~ (v4_relat_1 @ X8 @ X9)
% 3.42/3.61          | ~ (v1_relat_1 @ X8))),
% 3.42/3.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.42/3.61  thf('44', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (v1_relat_1 @ k1_xboole_0)
% 3.42/3.61          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['42', '43'])).
% 3.42/3.61  thf('45', plain,
% 3.42/3.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['33', '34'])).
% 3.42/3.61  thf(cc1_relset_1, axiom,
% 3.42/3.61    (![A:$i,B:$i,C:$i]:
% 3.42/3.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.42/3.61       ( v1_relat_1 @ C ) ))).
% 3.42/3.61  thf('46', plain,
% 3.42/3.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.42/3.61         ((v1_relat_1 @ X14)
% 3.42/3.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.42/3.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.42/3.61  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.42/3.61      inference('sup-', [status(thm)], ['45', '46'])).
% 3.42/3.61  thf('48', plain,
% 3.42/3.61      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['44', '47'])).
% 3.42/3.61  thf('49', plain,
% 3.42/3.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.42/3.61         (((k1_xboole_0) = (k7_relat_1 @ X0 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.42/3.61      inference('sup+', [status(thm)], ['39', '48'])).
% 3.42/3.61  thf('50', plain,
% 3.42/3.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.42/3.61         (((X28) != (k1_xboole_0))
% 3.42/3.61          | ((X29) = (k1_xboole_0))
% 3.42/3.61          | (v1_funct_2 @ X30 @ X29 @ X28)
% 3.42/3.61          | ((X30) != (k1_xboole_0))
% 3.42/3.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.42/3.61  thf('51', plain,
% 3.42/3.61      (![X29 : $i]:
% 3.42/3.61         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.42/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ k1_xboole_0)))
% 3.42/3.61          | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)
% 3.42/3.61          | ((X29) = (k1_xboole_0)))),
% 3.42/3.61      inference('simplify', [status(thm)], ['50'])).
% 3.42/3.61  thf('52', plain,
% 3.42/3.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['33', '34'])).
% 3.42/3.61  thf('53', plain,
% 3.42/3.61      (![X29 : $i]:
% 3.42/3.61         ((v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)
% 3.42/3.61          | ((X29) = (k1_xboole_0)))),
% 3.42/3.61      inference('demod', [status(thm)], ['51', '52'])).
% 3.42/3.61  thf('54', plain,
% 3.42/3.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.42/3.61         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 3.42/3.61          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 3.42/3.61          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.42/3.61  thf('55', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (((X0) = (k1_xboole_0))
% 3.42/3.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.42/3.61          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['53', '54'])).
% 3.42/3.61  thf('56', plain,
% 3.42/3.61      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['33', '34'])).
% 3.42/3.61  thf('57', plain,
% 3.42/3.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.42/3.61         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 3.42/3.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.42/3.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.42/3.61  thf('58', plain,
% 3.42/3.61      (![X0 : $i, X1 : $i]:
% 3.42/3.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['56', '57'])).
% 3.42/3.61  thf('59', plain,
% 3.42/3.61      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['44', '47'])).
% 3.42/3.61  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.42/3.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.42/3.61  thf(t91_relat_1, axiom,
% 3.42/3.61    (![A:$i,B:$i]:
% 3.42/3.61     ( ( v1_relat_1 @ B ) =>
% 3.42/3.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.42/3.61         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.42/3.61  thf('61', plain,
% 3.42/3.61      (![X12 : $i, X13 : $i]:
% 3.42/3.61         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 3.42/3.61          | ~ (v1_relat_1 @ X13))),
% 3.42/3.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.42/3.61  thf('62', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (v1_relat_1 @ X0)
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['60', '61'])).
% 3.42/3.61  thf('63', plain,
% 3.42/3.61      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.42/3.61        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.42/3.61      inference('sup+', [status(thm)], ['59', '62'])).
% 3.42/3.61  thf('64', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.42/3.61      inference('sup-', [status(thm)], ['45', '46'])).
% 3.42/3.61  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.61      inference('demod', [status(thm)], ['63', '64'])).
% 3.42/3.61  thf('66', plain,
% 3.42/3.61      (![X0 : $i, X1 : $i]:
% 3.42/3.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.61      inference('demod', [status(thm)], ['58', '65'])).
% 3.42/3.61  thf('67', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (((X0) = (k1_xboole_0))
% 3.42/3.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.42/3.61          | ((X0) = (k1_xboole_0)))),
% 3.42/3.61      inference('demod', [status(thm)], ['55', '66'])).
% 3.42/3.61  thf('68', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.42/3.61          | ((X0) = (k1_xboole_0)))),
% 3.42/3.61      inference('simplify', [status(thm)], ['67'])).
% 3.42/3.61  thf('69', plain,
% 3.42/3.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.42/3.61         (~ (zip_tseitin_1 @ k1_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.42/3.61          | (zip_tseitin_0 @ X1 @ X3)
% 3.42/3.61          | ((X2) = (k1_xboole_0)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['49', '68'])).
% 3.42/3.61  thf('70', plain,
% 3.42/3.61      (![X1 : $i, X2 : $i]:
% 3.42/3.61         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.42/3.61          | ((sk_B) = (k1_xboole_0))
% 3.42/3.61          | (zip_tseitin_0 @ X1 @ X2))),
% 3.42/3.61      inference('sup-', [status(thm)], ['38', '69'])).
% 3.42/3.61  thf('71', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('72', plain,
% 3.42/3.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.42/3.61      inference('split', [status(esa)], ['71'])).
% 3.42/3.61  thf('73', plain,
% 3.42/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('split', [status(esa)], ['71'])).
% 3.42/3.61  thf('74', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('75', plain,
% 3.42/3.61      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup+', [status(thm)], ['73', '74'])).
% 3.42/3.61  thf('76', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.61      inference('demod', [status(thm)], ['63', '64'])).
% 3.42/3.61  thf('77', plain,
% 3.42/3.61      (![X12 : $i, X13 : $i]:
% 3.42/3.61         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 3.42/3.61          | ~ (v1_relat_1 @ X13))),
% 3.42/3.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.42/3.61  thf('78', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 3.42/3.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['76', '77'])).
% 3.42/3.61  thf('79', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.42/3.61      inference('sup-', [status(thm)], ['45', '46'])).
% 3.42/3.61  thf('80', plain,
% 3.42/3.61      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['44', '47'])).
% 3.42/3.61  thf('81', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.42/3.61      inference('demod', [status(thm)], ['63', '64'])).
% 3.42/3.61  thf('82', plain,
% 3.42/3.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 3.42/3.61      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 3.42/3.61  thf('83', plain,
% 3.42/3.61      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['75', '82'])).
% 3.42/3.61  thf('84', plain,
% 3.42/3.61      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 3.42/3.61        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.42/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 3.42/3.61      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 3.42/3.61  thf('85', plain,
% 3.42/3.61      (((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 3.42/3.61            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 3.42/3.61         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['83', '84'])).
% 3.42/3.61  thf('86', plain,
% 3.42/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('split', [status(esa)], ['71'])).
% 3.42/3.61  thf('87', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('88', plain,
% 3.42/3.61      (((m1_subset_1 @ sk_D @ 
% 3.42/3.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup+', [status(thm)], ['86', '87'])).
% 3.42/3.61  thf('89', plain,
% 3.42/3.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.42/3.61         ((v4_relat_1 @ X17 @ X18)
% 3.42/3.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.42/3.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.42/3.61  thf('90', plain,
% 3.42/3.61      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['88', '89'])).
% 3.42/3.61  thf('91', plain,
% 3.42/3.61      (![X8 : $i, X9 : $i]:
% 3.42/3.61         (((X8) = (k7_relat_1 @ X8 @ X9))
% 3.42/3.61          | ~ (v4_relat_1 @ X8 @ X9)
% 3.42/3.61          | ~ (v1_relat_1 @ X8))),
% 3.42/3.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.42/3.61  thf('92', plain,
% 3.42/3.61      (((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0))))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['90', '91'])).
% 3.42/3.61  thf('93', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('94', plain,
% 3.42/3.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.42/3.61         ((v1_relat_1 @ X14)
% 3.42/3.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.42/3.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.42/3.61  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 3.42/3.61      inference('sup-', [status(thm)], ['93', '94'])).
% 3.42/3.61  thf('96', plain,
% 3.42/3.61      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('demod', [status(thm)], ['92', '95'])).
% 3.42/3.61  thf('97', plain,
% 3.42/3.61      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['75', '82'])).
% 3.42/3.61  thf('98', plain,
% 3.42/3.61      (((m1_subset_1 @ sk_D @ 
% 3.42/3.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup+', [status(thm)], ['86', '87'])).
% 3.42/3.61  thf('99', plain,
% 3.42/3.61      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['75', '82'])).
% 3.42/3.61  thf('100', plain,
% 3.42/3.61      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('demod', [status(thm)], ['92', '95'])).
% 3.42/3.61  thf('101', plain,
% 3.42/3.61      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['75', '82'])).
% 3.42/3.61  thf('102', plain,
% 3.42/3.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('split', [status(esa)], ['71'])).
% 3.42/3.61  thf('103', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('104', plain,
% 3.42/3.61      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 3.42/3.61         <= ((((sk_A) = (k1_xboole_0))))),
% 3.42/3.61      inference('sup+', [status(thm)], ['102', '103'])).
% 3.42/3.61  thf('105', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.42/3.61      inference('demod', [status(thm)],
% 3.42/3.61                ['85', '96', '97', '98', '99', '100', '101', '104'])).
% 3.42/3.61  thf('106', plain,
% 3.42/3.61      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.42/3.61      inference('split', [status(esa)], ['71'])).
% 3.42/3.61  thf('107', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 3.42/3.61      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 3.42/3.61  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 3.42/3.61      inference('simpl_trail', [status(thm)], ['72', '107'])).
% 3.42/3.61  thf('109', plain,
% 3.42/3.61      (![X1 : $i, X2 : $i]:
% 3.42/3.61         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X2))),
% 3.42/3.61      inference('simplify_reflect-', [status(thm)], ['70', '108'])).
% 3.42/3.61  thf('110', plain,
% 3.42/3.61      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.42/3.61      inference('sup-', [status(thm)], ['21', '22'])).
% 3.42/3.61  thf('111', plain,
% 3.42/3.61      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.42/3.61      inference('sup-', [status(thm)], ['109', '110'])).
% 3.42/3.61  thf('112', plain,
% 3.42/3.61      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.42/3.61      inference('demod', [status(thm)], ['27', '30'])).
% 3.42/3.61  thf('113', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.42/3.61      inference('clc', [status(thm)], ['111', '112'])).
% 3.42/3.61  thf('114', plain,
% 3.42/3.61      (![X12 : $i, X13 : $i]:
% 3.42/3.61         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 3.42/3.61          | ~ (v1_relat_1 @ X13))),
% 3.42/3.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.42/3.61  thf('115', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (r1_tarski @ X0 @ sk_A)
% 3.42/3.61          | ~ (v1_relat_1 @ sk_D)
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 3.42/3.61      inference('sup-', [status(thm)], ['113', '114'])).
% 3.42/3.61  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 3.42/3.61      inference('sup-', [status(thm)], ['93', '94'])).
% 3.42/3.61  thf('117', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (r1_tarski @ X0 @ sk_A)
% 3.42/3.61          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 3.42/3.61      inference('demod', [status(thm)], ['115', '116'])).
% 3.42/3.61  thf('118', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 3.42/3.61      inference('sup-', [status(thm)], ['16', '117'])).
% 3.42/3.61  thf('119', plain,
% 3.42/3.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('120', plain,
% 3.42/3.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.42/3.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.42/3.61          | ~ (v1_funct_1 @ X31)
% 3.42/3.61          | (m1_subset_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34) @ 
% 3.42/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 3.42/3.61      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 3.42/3.61  thf('121', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 3.42/3.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.42/3.61          | ~ (v1_funct_1 @ sk_D))),
% 3.42/3.61      inference('sup-', [status(thm)], ['119', '120'])).
% 3.42/3.61  thf('122', plain, ((v1_funct_1 @ sk_D)),
% 3.42/3.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.42/3.61  thf('123', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 3.42/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('demod', [status(thm)], ['121', '122'])).
% 3.42/3.61  thf('124', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['3', '4'])).
% 3.42/3.61  thf('125', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.42/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('demod', [status(thm)], ['123', '124'])).
% 3.42/3.61  thf('126', plain,
% 3.42/3.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.42/3.61         ((v5_relat_1 @ X17 @ X19)
% 3.42/3.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.42/3.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.42/3.61  thf('127', plain,
% 3.42/3.61      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 3.42/3.61      inference('sup-', [status(thm)], ['125', '126'])).
% 3.42/3.61  thf(d19_relat_1, axiom,
% 3.42/3.61    (![A:$i,B:$i]:
% 3.42/3.61     ( ( v1_relat_1 @ B ) =>
% 3.42/3.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.42/3.61  thf('128', plain,
% 3.42/3.61      (![X6 : $i, X7 : $i]:
% 3.42/3.61         (~ (v5_relat_1 @ X6 @ X7)
% 3.42/3.61          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 3.42/3.61          | ~ (v1_relat_1 @ X6))),
% 3.42/3.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.42/3.61  thf('129', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.42/3.61          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 3.42/3.61      inference('sup-', [status(thm)], ['127', '128'])).
% 3.42/3.61  thf('130', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.42/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.42/3.61      inference('demod', [status(thm)], ['123', '124'])).
% 3.42/3.61  thf('131', plain,
% 3.42/3.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.42/3.61         ((v1_relat_1 @ X14)
% 3.42/3.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.42/3.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.42/3.61  thf('132', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['130', '131'])).
% 3.42/3.61  thf('133', plain,
% 3.42/3.61      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.42/3.61      inference('demod', [status(thm)], ['129', '132'])).
% 3.42/3.61  thf(t4_funct_2, axiom,
% 3.42/3.61    (![A:$i,B:$i]:
% 3.42/3.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.42/3.61       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.42/3.61         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 3.42/3.61           ( m1_subset_1 @
% 3.42/3.61             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 3.42/3.61  thf('134', plain,
% 3.42/3.61      (![X39 : $i, X40 : $i]:
% 3.42/3.61         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 3.42/3.61          | (v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ X40)
% 3.42/3.61          | ~ (v1_funct_1 @ X39)
% 3.42/3.61          | ~ (v1_relat_1 @ X39))),
% 3.42/3.61      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.42/3.61  thf('135', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.42/3.61          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.42/3.61          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.42/3.61             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 3.42/3.61      inference('sup-', [status(thm)], ['133', '134'])).
% 3.42/3.61  thf('136', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['130', '131'])).
% 3.42/3.61  thf('137', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['10', '11'])).
% 3.42/3.61  thf('138', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.42/3.61          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.42/3.61      inference('demod', [status(thm)], ['135', '136', '137'])).
% 3.42/3.61  thf('139', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 3.42/3.61      inference('sup+', [status(thm)], ['118', '138'])).
% 3.42/3.61  thf('140', plain,
% 3.42/3.61      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.42/3.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 3.42/3.61      inference('demod', [status(thm)], ['15', '139'])).
% 3.42/3.61  thf('141', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 3.42/3.61      inference('sup-', [status(thm)], ['16', '117'])).
% 3.42/3.61  thf('142', plain,
% 3.42/3.61      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 3.42/3.61      inference('demod', [status(thm)], ['129', '132'])).
% 3.42/3.61  thf('143', plain,
% 3.42/3.61      (![X39 : $i, X40 : $i]:
% 3.42/3.61         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 3.42/3.61          | (m1_subset_1 @ X39 @ 
% 3.42/3.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 3.42/3.61          | ~ (v1_funct_1 @ X39)
% 3.42/3.61          | ~ (v1_relat_1 @ X39))),
% 3.42/3.61      inference('cnf', [status(esa)], [t4_funct_2])).
% 3.42/3.61  thf('144', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.42/3.61          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 3.42/3.61          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.42/3.61             (k1_zfmisc_1 @ 
% 3.42/3.61              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 3.42/3.61      inference('sup-', [status(thm)], ['142', '143'])).
% 3.42/3.61  thf('145', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('sup-', [status(thm)], ['130', '131'])).
% 3.42/3.61  thf('146', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 3.42/3.61      inference('demod', [status(thm)], ['10', '11'])).
% 3.42/3.61  thf('147', plain,
% 3.42/3.61      (![X0 : $i]:
% 3.42/3.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 3.42/3.61          (k1_zfmisc_1 @ 
% 3.42/3.61           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 3.42/3.61      inference('demod', [status(thm)], ['144', '145', '146'])).
% 3.42/3.61  thf('148', plain,
% 3.42/3.61      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 3.42/3.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 3.42/3.61      inference('sup+', [status(thm)], ['141', '147'])).
% 3.42/3.61  thf('149', plain, ($false), inference('demod', [status(thm)], ['140', '148'])).
% 3.42/3.61  
% 3.42/3.61  % SZS output end Refutation
% 3.42/3.61  
% 3.42/3.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
