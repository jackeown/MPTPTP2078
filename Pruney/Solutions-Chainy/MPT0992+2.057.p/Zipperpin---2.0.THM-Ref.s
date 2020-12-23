%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xtJ4NJ3BsS

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:42 EST 2020

% Result     : Theorem 19.16s
% Output     : Refutation 19.16s
% Verified   : 
% Statistics : Number of formulae       :  223 (1064 expanded)
%              Number of leaves         :   44 ( 330 expanded)
%              Depth                    :   21
%              Number of atoms          : 1692 (15707 expanded)
%              Number of equality atoms :  129 ( 915 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X46 @ X47 @ X45 @ X48 )
        = ( k7_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','29'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','41'])).

thf('43',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','68'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('73',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('75',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('77',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('82',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('85',plain,(
    ! [X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('89',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ( X40 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,(
    ! [X39: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('99',plain,(
    ! [X39: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','97','98'])).

thf('100',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('106',plain,(
    ! [X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('107',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('112',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','115'])).

thf('117',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['116'])).

thf('118',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('119',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('121',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('122',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('123',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['116'])).

thf('124',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','112'])).

thf('126',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('130',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('132',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['128','132'])).

thf('134',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['75','80','117','118','119','120','121','122','123','124','133'])).

thf('135',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('136',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['134','135'])).

thf('137',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','136'])).

thf('138',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['61','137'])).

thf('139',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['50','138'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('140',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['43','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('146',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('151',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('155',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('159',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('161',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['157','158'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('166',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','168'])).

thf('170',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','136'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(condensation,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['152','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','173'])).

thf('175',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['144','174'])).

thf('176',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['42','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xtJ4NJ3BsS
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 19.16/19.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.16/19.40  % Solved by: fo/fo7.sh
% 19.16/19.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.16/19.40  % done 12239 iterations in 18.923s
% 19.16/19.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.16/19.40  % SZS output start Refutation
% 19.16/19.40  thf(sk_C_type, type, sk_C: $i).
% 19.16/19.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.16/19.40  thf(sk_A_type, type, sk_A: $i).
% 19.16/19.40  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 19.16/19.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.16/19.40  thf(sk_B_type, type, sk_B: $i).
% 19.16/19.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 19.16/19.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.16/19.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 19.16/19.40  thf(sk_D_type, type, sk_D: $i).
% 19.16/19.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.16/19.40  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 19.16/19.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 19.16/19.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 19.16/19.40  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 19.16/19.40  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 19.16/19.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.16/19.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 19.16/19.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.16/19.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.16/19.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.16/19.40  thf(t38_funct_2, conjecture,
% 19.16/19.40    (![A:$i,B:$i,C:$i,D:$i]:
% 19.16/19.40     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 19.16/19.40         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.16/19.40       ( ( r1_tarski @ C @ A ) =>
% 19.16/19.40         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 19.16/19.40           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 19.16/19.40             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 19.16/19.40             ( m1_subset_1 @
% 19.16/19.40               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 19.16/19.40               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 19.16/19.40  thf(zf_stmt_0, negated_conjecture,
% 19.16/19.40    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 19.16/19.40        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 19.16/19.40            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.16/19.40          ( ( r1_tarski @ C @ A ) =>
% 19.16/19.40            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 19.16/19.40              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 19.16/19.40                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 19.16/19.40                ( m1_subset_1 @
% 19.16/19.40                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 19.16/19.40                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 19.16/19.40    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 19.16/19.40  thf('0', plain,
% 19.16/19.40      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 19.16/19.40        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 19.16/19.40             sk_B)
% 19.16/19.40        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('1', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf(dt_k2_partfun1, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i,D:$i]:
% 19.16/19.40     ( ( ( v1_funct_1 @ C ) & 
% 19.16/19.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.16/19.40       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 19.16/19.40         ( m1_subset_1 @
% 19.16/19.40           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 19.16/19.40           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 19.16/19.40  thf('2', plain,
% 19.16/19.40      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 19.16/19.40         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 19.16/19.40          | ~ (v1_funct_1 @ X41)
% 19.16/19.40          | (v1_funct_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44)))),
% 19.16/19.40      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 19.16/19.40  thf('3', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 19.16/19.40          | ~ (v1_funct_1 @ sk_D))),
% 19.16/19.40      inference('sup-', [status(thm)], ['1', '2'])).
% 19.16/19.40  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('5', plain,
% 19.16/19.40      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 19.16/19.40      inference('demod', [status(thm)], ['3', '4'])).
% 19.16/19.40  thf('6', plain,
% 19.16/19.40      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 19.16/19.40        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 19.16/19.40      inference('demod', [status(thm)], ['0', '5'])).
% 19.16/19.40  thf('7', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf(redefinition_k2_partfun1, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i,D:$i]:
% 19.16/19.40     ( ( ( v1_funct_1 @ C ) & 
% 19.16/19.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.16/19.40       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 19.16/19.40  thf('8', plain,
% 19.16/19.40      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 19.16/19.40         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 19.16/19.40          | ~ (v1_funct_1 @ X45)
% 19.16/19.40          | ((k2_partfun1 @ X46 @ X47 @ X45 @ X48) = (k7_relat_1 @ X45 @ X48)))),
% 19.16/19.40      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 19.16/19.40  thf('9', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 19.16/19.40          | ~ (v1_funct_1 @ sk_D))),
% 19.16/19.40      inference('sup-', [status(thm)], ['7', '8'])).
% 19.16/19.40  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('11', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 19.16/19.40      inference('demod', [status(thm)], ['9', '10'])).
% 19.16/19.40  thf('12', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 19.16/19.40      inference('demod', [status(thm)], ['9', '10'])).
% 19.16/19.40  thf('13', plain,
% 19.16/19.40      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 19.16/19.40        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 19.16/19.40      inference('demod', [status(thm)], ['6', '11', '12'])).
% 19.16/19.40  thf('14', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('15', plain,
% 19.16/19.40      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 19.16/19.40         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 19.16/19.40          | ~ (v1_funct_1 @ X41)
% 19.16/19.40          | (m1_subset_1 @ (k2_partfun1 @ X42 @ X43 @ X41 @ X44) @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 19.16/19.40      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 19.16/19.40  thf('16', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 19.16/19.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 19.16/19.40          | ~ (v1_funct_1 @ sk_D))),
% 19.16/19.40      inference('sup-', [status(thm)], ['14', '15'])).
% 19.16/19.40  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('18', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 19.16/19.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('demod', [status(thm)], ['16', '17'])).
% 19.16/19.40  thf('19', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 19.16/19.40      inference('demod', [status(thm)], ['9', '10'])).
% 19.16/19.40  thf('20', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 19.16/19.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('demod', [status(thm)], ['18', '19'])).
% 19.16/19.40  thf(cc2_relset_1, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i]:
% 19.16/19.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.16/19.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 19.16/19.40  thf('21', plain,
% 19.16/19.40      (![X24 : $i, X25 : $i, X26 : $i]:
% 19.16/19.40         ((v5_relat_1 @ X24 @ X26)
% 19.16/19.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 19.16/19.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 19.16/19.40  thf('22', plain,
% 19.16/19.40      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 19.16/19.40      inference('sup-', [status(thm)], ['20', '21'])).
% 19.16/19.40  thf(d19_relat_1, axiom,
% 19.16/19.40    (![A:$i,B:$i]:
% 19.16/19.40     ( ( v1_relat_1 @ B ) =>
% 19.16/19.40       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 19.16/19.40  thf('23', plain,
% 19.16/19.40      (![X13 : $i, X14 : $i]:
% 19.16/19.40         (~ (v5_relat_1 @ X13 @ X14)
% 19.16/19.40          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 19.16/19.40          | ~ (v1_relat_1 @ X13))),
% 19.16/19.40      inference('cnf', [status(esa)], [d19_relat_1])).
% 19.16/19.40  thf('24', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 19.16/19.40          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 19.16/19.40      inference('sup-', [status(thm)], ['22', '23'])).
% 19.16/19.40  thf('25', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 19.16/19.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('demod', [status(thm)], ['18', '19'])).
% 19.16/19.40  thf(cc2_relat_1, axiom,
% 19.16/19.40    (![A:$i]:
% 19.16/19.40     ( ( v1_relat_1 @ A ) =>
% 19.16/19.40       ( ![B:$i]:
% 19.16/19.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 19.16/19.40  thf('26', plain,
% 19.16/19.40      (![X11 : $i, X12 : $i]:
% 19.16/19.40         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 19.16/19.40          | (v1_relat_1 @ X11)
% 19.16/19.40          | ~ (v1_relat_1 @ X12))),
% 19.16/19.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.16/19.40  thf('27', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 19.16/19.40          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['25', '26'])).
% 19.16/19.40  thf(fc6_relat_1, axiom,
% 19.16/19.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 19.16/19.40  thf('28', plain,
% 19.16/19.40      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 19.16/19.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.16/19.40  thf('29', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 19.16/19.40      inference('demod', [status(thm)], ['27', '28'])).
% 19.16/19.40  thf('30', plain,
% 19.16/19.40      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 19.16/19.40      inference('demod', [status(thm)], ['24', '29'])).
% 19.16/19.40  thf(t87_relat_1, axiom,
% 19.16/19.40    (![A:$i,B:$i]:
% 19.16/19.40     ( ( v1_relat_1 @ B ) =>
% 19.16/19.40       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 19.16/19.40  thf('31', plain,
% 19.16/19.40      (![X20 : $i, X21 : $i]:
% 19.16/19.40         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ X21)
% 19.16/19.40          | ~ (v1_relat_1 @ X20))),
% 19.16/19.40      inference('cnf', [status(esa)], [t87_relat_1])).
% 19.16/19.40  thf(t11_relset_1, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i]:
% 19.16/19.40     ( ( v1_relat_1 @ C ) =>
% 19.16/19.40       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 19.16/19.40           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 19.16/19.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 19.16/19.40  thf('32', plain,
% 19.16/19.40      (![X30 : $i, X31 : $i, X32 : $i]:
% 19.16/19.40         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 19.16/19.40          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 19.16/19.40          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 19.16/19.40          | ~ (v1_relat_1 @ X30))),
% 19.16/19.40      inference('cnf', [status(esa)], [t11_relset_1])).
% 19.16/19.40  thf('33', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.16/19.40         (~ (v1_relat_1 @ X1)
% 19.16/19.40          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 19.16/19.40          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 19.16/19.40          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 19.16/19.40      inference('sup-', [status(thm)], ['31', '32'])).
% 19.16/19.40  thf('34', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 19.16/19.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 19.16/19.40          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 19.16/19.40          | ~ (v1_relat_1 @ sk_D))),
% 19.16/19.40      inference('sup-', [status(thm)], ['30', '33'])).
% 19.16/19.40  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 19.16/19.40      inference('demod', [status(thm)], ['27', '28'])).
% 19.16/19.40  thf('36', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('37', plain,
% 19.16/19.40      (![X11 : $i, X12 : $i]:
% 19.16/19.40         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 19.16/19.40          | (v1_relat_1 @ X11)
% 19.16/19.40          | ~ (v1_relat_1 @ X12))),
% 19.16/19.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.16/19.40  thf('38', plain,
% 19.16/19.40      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 19.16/19.40      inference('sup-', [status(thm)], ['36', '37'])).
% 19.16/19.40  thf('39', plain,
% 19.16/19.40      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 19.16/19.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.16/19.40  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 19.16/19.40      inference('demod', [status(thm)], ['38', '39'])).
% 19.16/19.40  thf('41', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 19.16/19.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 19.16/19.40      inference('demod', [status(thm)], ['34', '35', '40'])).
% 19.16/19.40  thf('42', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 19.16/19.40      inference('demod', [status(thm)], ['13', '41'])).
% 19.16/19.40  thf('43', plain, ((r1_tarski @ sk_C @ sk_A)),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf(d1_funct_2, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i]:
% 19.16/19.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.16/19.40       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.16/19.40           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 19.16/19.40             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 19.16/19.40         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.16/19.40           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 19.16/19.40             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 19.16/19.40  thf(zf_stmt_1, axiom,
% 19.16/19.40    (![C:$i,B:$i,A:$i]:
% 19.16/19.40     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 19.16/19.40       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 19.16/19.40  thf('45', plain,
% 19.16/19.40      (![X35 : $i, X36 : $i, X37 : $i]:
% 19.16/19.40         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 19.16/19.40          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 19.16/19.40          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.16/19.40  thf('46', plain,
% 19.16/19.40      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 19.16/19.40        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['44', '45'])).
% 19.16/19.40  thf('47', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf(redefinition_k1_relset_1, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i]:
% 19.16/19.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.16/19.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 19.16/19.40  thf('48', plain,
% 19.16/19.40      (![X27 : $i, X28 : $i, X29 : $i]:
% 19.16/19.40         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 19.16/19.40          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 19.16/19.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.16/19.40  thf('49', plain,
% 19.16/19.40      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 19.16/19.40      inference('sup-', [status(thm)], ['47', '48'])).
% 19.16/19.40  thf('50', plain,
% 19.16/19.40      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 19.16/19.40      inference('demod', [status(thm)], ['46', '49'])).
% 19.16/19.40  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.16/19.40  thf('51', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 19.16/19.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.16/19.40  thf(zf_stmt_2, axiom,
% 19.16/19.40    (![B:$i,A:$i]:
% 19.16/19.40     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.16/19.40       ( zip_tseitin_0 @ B @ A ) ))).
% 19.16/19.40  thf('52', plain,
% 19.16/19.40      (![X33 : $i, X34 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.16/19.40  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 19.16/19.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.16/19.40  thf('54', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.16/19.40         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 19.16/19.40      inference('sup+', [status(thm)], ['52', '53'])).
% 19.16/19.40  thf('55', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 19.16/19.40  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 19.16/19.40  thf(zf_stmt_5, axiom,
% 19.16/19.40    (![A:$i,B:$i,C:$i]:
% 19.16/19.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.16/19.40       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 19.16/19.40         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.16/19.40           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 19.16/19.40             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 19.16/19.40  thf('56', plain,
% 19.16/19.40      (![X38 : $i, X39 : $i, X40 : $i]:
% 19.16/19.40         (~ (zip_tseitin_0 @ X38 @ X39)
% 19.16/19.40          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 19.16/19.40          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.16/19.40  thf('57', plain,
% 19.16/19.40      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 19.16/19.40      inference('sup-', [status(thm)], ['55', '56'])).
% 19.16/19.40  thf('58', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 19.16/19.40      inference('sup-', [status(thm)], ['54', '57'])).
% 19.16/19.40  thf(d10_xboole_0, axiom,
% 19.16/19.40    (![A:$i,B:$i]:
% 19.16/19.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.16/19.40  thf('59', plain,
% 19.16/19.40      (![X0 : $i, X2 : $i]:
% 19.16/19.40         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.16/19.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.16/19.40  thf('60', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 19.16/19.40          | ~ (r1_tarski @ X0 @ sk_B)
% 19.16/19.40          | ((X0) = (sk_B)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['58', '59'])).
% 19.16/19.40  thf('61', plain,
% 19.16/19.40      ((((k1_xboole_0) = (sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 19.16/19.40      inference('sup-', [status(thm)], ['51', '60'])).
% 19.16/19.40  thf('62', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('63', plain,
% 19.16/19.40      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 19.16/19.40      inference('split', [status(esa)], ['62'])).
% 19.16/19.40  thf('64', plain,
% 19.16/19.40      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('split', [status(esa)], ['62'])).
% 19.16/19.40  thf('65', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('66', plain,
% 19.16/19.40      (((m1_subset_1 @ sk_D @ 
% 19.16/19.40         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 19.16/19.40         <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup+', [status(thm)], ['64', '65'])).
% 19.16/19.40  thf(t113_zfmisc_1, axiom,
% 19.16/19.40    (![A:$i,B:$i]:
% 19.16/19.40     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 19.16/19.40       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 19.16/19.40  thf('67', plain,
% 19.16/19.40      (![X6 : $i, X7 : $i]:
% 19.16/19.40         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 19.16/19.40  thf('68', plain,
% 19.16/19.40      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 19.16/19.40      inference('simplify', [status(thm)], ['67'])).
% 19.16/19.40  thf('69', plain,
% 19.16/19.40      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 19.16/19.40         <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('demod', [status(thm)], ['66', '68'])).
% 19.16/19.40  thf(t3_subset, axiom,
% 19.16/19.40    (![A:$i,B:$i]:
% 19.16/19.40     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 19.16/19.40  thf('70', plain,
% 19.16/19.40      (![X8 : $i, X9 : $i]:
% 19.16/19.40         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 19.16/19.40      inference('cnf', [status(esa)], [t3_subset])).
% 19.16/19.40  thf('71', plain,
% 19.16/19.40      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['69', '70'])).
% 19.16/19.40  thf(t3_xboole_1, axiom,
% 19.16/19.40    (![A:$i]:
% 19.16/19.40     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 19.16/19.40  thf('72', plain,
% 19.16/19.40      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 19.16/19.40      inference('cnf', [status(esa)], [t3_xboole_1])).
% 19.16/19.40  thf('73', plain,
% 19.16/19.40      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['71', '72'])).
% 19.16/19.40  thf('74', plain,
% 19.16/19.40      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 19.16/19.40        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 19.16/19.40      inference('demod', [status(thm)], ['6', '11', '12'])).
% 19.16/19.40  thf('75', plain,
% 19.16/19.40      (((~ (m1_subset_1 @ (k7_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 19.16/19.40            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 19.16/19.40         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 19.16/19.40         <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['73', '74'])).
% 19.16/19.40  thf('76', plain,
% 19.16/19.40      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('split', [status(esa)], ['62'])).
% 19.16/19.40  thf('77', plain, ((r1_tarski @ sk_C @ sk_A)),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('78', plain,
% 19.16/19.40      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup+', [status(thm)], ['76', '77'])).
% 19.16/19.40  thf('79', plain,
% 19.16/19.40      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 19.16/19.40      inference('cnf', [status(esa)], [t3_xboole_1])).
% 19.16/19.40  thf('80', plain,
% 19.16/19.40      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['78', '79'])).
% 19.16/19.40  thf('81', plain,
% 19.16/19.40      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 19.16/19.40      inference('simplify', [status(thm)], ['67'])).
% 19.16/19.40  thf('82', plain,
% 19.16/19.40      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 19.16/19.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.16/19.40  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 19.16/19.40      inference('sup+', [status(thm)], ['81', '82'])).
% 19.16/19.40  thf('84', plain,
% 19.16/19.40      (![X33 : $i, X34 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.16/19.40  thf(t110_relat_1, axiom,
% 19.16/19.40    (![A:$i]:
% 19.16/19.40     ( ( v1_relat_1 @ A ) =>
% 19.16/19.40       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 19.16/19.40  thf('85', plain,
% 19.16/19.40      (![X19 : $i]:
% 19.16/19.40         (((k7_relat_1 @ X19 @ k1_xboole_0) = (k1_xboole_0))
% 19.16/19.40          | ~ (v1_relat_1 @ X19))),
% 19.16/19.40      inference('cnf', [status(esa)], [t110_relat_1])).
% 19.16/19.40  thf('86', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.16/19.40         (((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 19.16/19.40          | (zip_tseitin_0 @ X0 @ X2)
% 19.16/19.40          | ~ (v1_relat_1 @ X1))),
% 19.16/19.40      inference('sup+', [status(thm)], ['84', '85'])).
% 19.16/19.40  thf('87', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ X1 @ X0)
% 19.16/19.40          | ((k7_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['83', '86'])).
% 19.16/19.40  thf('88', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 19.16/19.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.16/19.40  thf('89', plain,
% 19.16/19.40      (![X8 : $i, X10 : $i]:
% 19.16/19.40         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 19.16/19.40      inference('cnf', [status(esa)], [t3_subset])).
% 19.16/19.40  thf('90', plain,
% 19.16/19.40      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['88', '89'])).
% 19.16/19.40  thf('91', plain,
% 19.16/19.40      (![X38 : $i, X39 : $i, X40 : $i]:
% 19.16/19.40         (~ (zip_tseitin_0 @ X38 @ X39)
% 19.16/19.40          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 19.16/19.40          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.16/19.40  thf('92', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 19.16/19.40      inference('sup-', [status(thm)], ['90', '91'])).
% 19.16/19.40  thf('93', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         (((k7_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 19.16/19.40          | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['87', '92'])).
% 19.16/19.40  thf('94', plain,
% 19.16/19.40      (![X38 : $i, X39 : $i, X40 : $i]:
% 19.16/19.40         (((X38) != (k1_xboole_0))
% 19.16/19.40          | ((X39) = (k1_xboole_0))
% 19.16/19.40          | (v1_funct_2 @ X40 @ X39 @ X38)
% 19.16/19.40          | ((X40) != (k1_xboole_0))
% 19.16/19.40          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.16/19.40  thf('95', plain,
% 19.16/19.40      (![X39 : $i]:
% 19.16/19.40         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 19.16/19.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 19.16/19.40          | (v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0)
% 19.16/19.40          | ((X39) = (k1_xboole_0)))),
% 19.16/19.40      inference('simplify', [status(thm)], ['94'])).
% 19.16/19.40  thf('96', plain,
% 19.16/19.40      (![X6 : $i, X7 : $i]:
% 19.16/19.40         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 19.16/19.40  thf('97', plain,
% 19.16/19.40      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 19.16/19.40      inference('simplify', [status(thm)], ['96'])).
% 19.16/19.40  thf('98', plain,
% 19.16/19.40      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['88', '89'])).
% 19.16/19.40  thf('99', plain,
% 19.16/19.40      (![X39 : $i]:
% 19.16/19.40         ((v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0)
% 19.16/19.40          | ((X39) = (k1_xboole_0)))),
% 19.16/19.40      inference('demod', [status(thm)], ['95', '97', '98'])).
% 19.16/19.40  thf('100', plain,
% 19.16/19.40      (![X35 : $i, X36 : $i, X37 : $i]:
% 19.16/19.40         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 19.16/19.40          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 19.16/19.40          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.16/19.40  thf('101', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((X0) = (k1_xboole_0))
% 19.16/19.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 19.16/19.40          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['99', '100'])).
% 19.16/19.40  thf('102', plain,
% 19.16/19.40      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['88', '89'])).
% 19.16/19.40  thf('103', plain,
% 19.16/19.40      (![X27 : $i, X28 : $i, X29 : $i]:
% 19.16/19.40         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 19.16/19.40          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 19.16/19.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.16/19.40  thf('104', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['102', '103'])).
% 19.16/19.40  thf('105', plain,
% 19.16/19.40      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 19.16/19.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 19.16/19.40  thf('106', plain,
% 19.16/19.40      (![X19 : $i]:
% 19.16/19.40         (((k7_relat_1 @ X19 @ k1_xboole_0) = (k1_xboole_0))
% 19.16/19.40          | ~ (v1_relat_1 @ X19))),
% 19.16/19.40      inference('cnf', [status(esa)], [t110_relat_1])).
% 19.16/19.40  thf('107', plain,
% 19.16/19.40      (![X20 : $i, X21 : $i]:
% 19.16/19.40         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ X21)
% 19.16/19.40          | ~ (v1_relat_1 @ X20))),
% 19.16/19.40      inference('cnf', [status(esa)], [t87_relat_1])).
% 19.16/19.40  thf('108', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 19.16/19.40          | ~ (v1_relat_1 @ X0)
% 19.16/19.40          | ~ (v1_relat_1 @ X0))),
% 19.16/19.40      inference('sup+', [status(thm)], ['106', '107'])).
% 19.16/19.40  thf('109', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (~ (v1_relat_1 @ X0)
% 19.16/19.40          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 19.16/19.40      inference('simplify', [status(thm)], ['108'])).
% 19.16/19.40  thf('110', plain, ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 19.16/19.40      inference('sup-', [status(thm)], ['105', '109'])).
% 19.16/19.40  thf('111', plain,
% 19.16/19.40      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 19.16/19.40      inference('cnf', [status(esa)], [t3_xboole_1])).
% 19.16/19.40  thf('112', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['110', '111'])).
% 19.16/19.40  thf('113', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 19.16/19.40      inference('demod', [status(thm)], ['104', '112'])).
% 19.16/19.40  thf('114', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((X0) = (k1_xboole_0))
% 19.16/19.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 19.16/19.40          | ((X0) = (k1_xboole_0)))),
% 19.16/19.40      inference('demod', [status(thm)], ['101', '113'])).
% 19.16/19.40  thf('115', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 19.16/19.40          | ((X0) = (k1_xboole_0)))),
% 19.16/19.40      inference('simplify', [status(thm)], ['114'])).
% 19.16/19.40  thf('116', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 19.16/19.40          | ((X0) = (k1_xboole_0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['93', '115'])).
% 19.16/19.40  thf('117', plain,
% 19.16/19.40      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 19.16/19.40      inference('condensation', [status(thm)], ['116'])).
% 19.16/19.40  thf('118', plain,
% 19.16/19.40      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['78', '79'])).
% 19.16/19.40  thf('119', plain,
% 19.16/19.40      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 19.16/19.40      inference('simplify', [status(thm)], ['67'])).
% 19.16/19.40  thf('120', plain,
% 19.16/19.40      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['88', '89'])).
% 19.16/19.40  thf('121', plain,
% 19.16/19.40      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['71', '72'])).
% 19.16/19.40  thf('122', plain,
% 19.16/19.40      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['78', '79'])).
% 19.16/19.40  thf('123', plain,
% 19.16/19.40      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 19.16/19.40      inference('condensation', [status(thm)], ['116'])).
% 19.16/19.40  thf('124', plain,
% 19.16/19.40      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 19.16/19.40      inference('sup-', [status(thm)], ['78', '79'])).
% 19.16/19.40  thf('125', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 19.16/19.40      inference('demod', [status(thm)], ['104', '112'])).
% 19.16/19.40  thf('126', plain,
% 19.16/19.40      (![X35 : $i, X36 : $i, X37 : $i]:
% 19.16/19.40         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 19.16/19.40          | (v1_funct_2 @ X37 @ X35 @ X36)
% 19.16/19.40          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.16/19.40  thf('127', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         (((X1) != (k1_xboole_0))
% 19.16/19.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 19.16/19.40          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['125', '126'])).
% 19.16/19.40  thf('128', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 19.16/19.40          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 19.16/19.40      inference('simplify', [status(thm)], ['127'])).
% 19.16/19.40  thf('129', plain,
% 19.16/19.40      (![X33 : $i, X34 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.16/19.40  thf('130', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 19.16/19.40      inference('simplify', [status(thm)], ['129'])).
% 19.16/19.40  thf('131', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 19.16/19.40      inference('sup-', [status(thm)], ['90', '91'])).
% 19.16/19.40  thf('132', plain,
% 19.16/19.40      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 19.16/19.40      inference('sup-', [status(thm)], ['130', '131'])).
% 19.16/19.40  thf('133', plain,
% 19.16/19.40      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 19.16/19.40      inference('demod', [status(thm)], ['128', '132'])).
% 19.16/19.40  thf('134', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 19.16/19.40      inference('demod', [status(thm)],
% 19.16/19.40                ['75', '80', '117', '118', '119', '120', '121', '122', '123', 
% 19.16/19.40                 '124', '133'])).
% 19.16/19.40  thf('135', plain,
% 19.16/19.40      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 19.16/19.40      inference('split', [status(esa)], ['62'])).
% 19.16/19.40  thf('136', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 19.16/19.40      inference('sat_resolution*', [status(thm)], ['134', '135'])).
% 19.16/19.40  thf('137', plain, (((sk_B) != (k1_xboole_0))),
% 19.16/19.40      inference('simpl_trail', [status(thm)], ['63', '136'])).
% 19.16/19.40  thf('138', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 19.16/19.40      inference('simplify_reflect-', [status(thm)], ['61', '137'])).
% 19.16/19.40  thf('139', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 19.16/19.40      inference('demod', [status(thm)], ['50', '138'])).
% 19.16/19.40  thf(t91_relat_1, axiom,
% 19.16/19.40    (![A:$i,B:$i]:
% 19.16/19.40     ( ( v1_relat_1 @ B ) =>
% 19.16/19.40       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 19.16/19.40         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 19.16/19.40  thf('140', plain,
% 19.16/19.40      (![X22 : $i, X23 : $i]:
% 19.16/19.40         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 19.16/19.40          | ((k1_relat_1 @ (k7_relat_1 @ X23 @ X22)) = (X22))
% 19.16/19.40          | ~ (v1_relat_1 @ X23))),
% 19.16/19.40      inference('cnf', [status(esa)], [t91_relat_1])).
% 19.16/19.40  thf('141', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (~ (r1_tarski @ X0 @ sk_A)
% 19.16/19.40          | ~ (v1_relat_1 @ sk_D)
% 19.16/19.40          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['139', '140'])).
% 19.16/19.40  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 19.16/19.40      inference('demod', [status(thm)], ['38', '39'])).
% 19.16/19.40  thf('143', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (~ (r1_tarski @ X0 @ sk_A)
% 19.16/19.40          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 19.16/19.40      inference('demod', [status(thm)], ['141', '142'])).
% 19.16/19.40  thf('144', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 19.16/19.40      inference('sup-', [status(thm)], ['43', '143'])).
% 19.16/19.40  thf('145', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 19.16/19.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 19.16/19.40      inference('demod', [status(thm)], ['34', '35', '40'])).
% 19.16/19.40  thf('146', plain,
% 19.16/19.40      (![X27 : $i, X28 : $i, X29 : $i]:
% 19.16/19.40         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 19.16/19.40          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 19.16/19.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.16/19.40  thf('147', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 19.16/19.40           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['145', '146'])).
% 19.16/19.40  thf('148', plain,
% 19.16/19.40      (![X35 : $i, X36 : $i, X37 : $i]:
% 19.16/19.40         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 19.16/19.40          | (v1_funct_2 @ X37 @ X35 @ X36)
% 19.16/19.40          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.16/19.40  thf('149', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 19.16/19.40          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 19.16/19.40          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 19.16/19.40      inference('sup-', [status(thm)], ['147', '148'])).
% 19.16/19.40  thf('150', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 19.16/19.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 19.16/19.40      inference('demod', [status(thm)], ['34', '35', '40'])).
% 19.16/19.40  thf('151', plain,
% 19.16/19.40      (![X38 : $i, X39 : $i, X40 : $i]:
% 19.16/19.40         (~ (zip_tseitin_0 @ X38 @ X39)
% 19.16/19.40          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 19.16/19.40          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.16/19.40  thf('152', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 19.16/19.40          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['150', '151'])).
% 19.16/19.40  thf('153', plain,
% 19.16/19.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.16/19.40  thf('154', plain,
% 19.16/19.40      (![X24 : $i, X25 : $i, X26 : $i]:
% 19.16/19.40         ((v5_relat_1 @ X24 @ X26)
% 19.16/19.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 19.16/19.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 19.16/19.40  thf('155', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 19.16/19.40      inference('sup-', [status(thm)], ['153', '154'])).
% 19.16/19.40  thf('156', plain,
% 19.16/19.40      (![X13 : $i, X14 : $i]:
% 19.16/19.40         (~ (v5_relat_1 @ X13 @ X14)
% 19.16/19.40          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 19.16/19.40          | ~ (v1_relat_1 @ X13))),
% 19.16/19.40      inference('cnf', [status(esa)], [d19_relat_1])).
% 19.16/19.40  thf('157', plain,
% 19.16/19.40      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 19.16/19.40      inference('sup-', [status(thm)], ['155', '156'])).
% 19.16/19.40  thf('158', plain, ((v1_relat_1 @ sk_D)),
% 19.16/19.40      inference('demod', [status(thm)], ['38', '39'])).
% 19.16/19.40  thf('159', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 19.16/19.40      inference('demod', [status(thm)], ['157', '158'])).
% 19.16/19.40  thf('160', plain,
% 19.16/19.40      (![X33 : $i, X34 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 19.16/19.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.16/19.40  thf('161', plain,
% 19.16/19.40      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 19.16/19.40      inference('cnf', [status(esa)], [t3_xboole_1])).
% 19.16/19.40  thf('162', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.16/19.40         (~ (r1_tarski @ X1 @ X0)
% 19.16/19.40          | (zip_tseitin_0 @ X0 @ X2)
% 19.16/19.40          | ((X1) = (k1_xboole_0)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['160', '161'])).
% 19.16/19.40  thf('163', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['159', '162'])).
% 19.16/19.40  thf('164', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 19.16/19.40      inference('demod', [status(thm)], ['157', '158'])).
% 19.16/19.40  thf('165', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.16/19.40         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 19.16/19.40      inference('sup+', [status(thm)], ['52', '53'])).
% 19.16/19.40  thf('166', plain,
% 19.16/19.40      (![X0 : $i, X2 : $i]:
% 19.16/19.40         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 19.16/19.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.16/19.40  thf('167', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 19.16/19.40      inference('sup-', [status(thm)], ['165', '166'])).
% 19.16/19.40  thf('168', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 19.16/19.40      inference('sup-', [status(thm)], ['164', '167'])).
% 19.16/19.40  thf('169', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         (((k1_xboole_0) = (sk_B))
% 19.16/19.40          | (zip_tseitin_0 @ sk_B @ X1)
% 19.16/19.40          | (zip_tseitin_0 @ sk_B @ X0))),
% 19.16/19.40      inference('sup+', [status(thm)], ['163', '168'])).
% 19.16/19.40  thf('170', plain, (((sk_B) != (k1_xboole_0))),
% 19.16/19.40      inference('simpl_trail', [status(thm)], ['63', '136'])).
% 19.16/19.40  thf('171', plain,
% 19.16/19.40      (![X0 : $i, X1 : $i]:
% 19.16/19.40         ((zip_tseitin_0 @ sk_B @ X1) | (zip_tseitin_0 @ sk_B @ X0))),
% 19.16/19.40      inference('simplify_reflect-', [status(thm)], ['169', '170'])).
% 19.16/19.40  thf('172', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 19.16/19.40      inference('condensation', [status(thm)], ['171'])).
% 19.16/19.40  thf('173', plain,
% 19.16/19.40      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 19.16/19.40      inference('demod', [status(thm)], ['152', '172'])).
% 19.16/19.40  thf('174', plain,
% 19.16/19.40      (![X0 : $i]:
% 19.16/19.40         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 19.16/19.40          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 19.16/19.40      inference('demod', [status(thm)], ['149', '173'])).
% 19.16/19.40  thf('175', plain,
% 19.16/19.40      ((((sk_C) != (sk_C))
% 19.16/19.40        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 19.16/19.40      inference('sup-', [status(thm)], ['144', '174'])).
% 19.16/19.40  thf('176', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 19.16/19.40      inference('simplify', [status(thm)], ['175'])).
% 19.16/19.40  thf('177', plain, ($false), inference('demod', [status(thm)], ['42', '176'])).
% 19.16/19.40  
% 19.16/19.40  % SZS output end Refutation
% 19.16/19.40  
% 19.16/19.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
