%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Au4t8JCzP

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:38 EST 2020

% Result     : Theorem 40.51s
% Output     : Refutation 40.51s
% Verified   : 
% Statistics : Number of formulae       :  218 (1157 expanded)
%              Number of leaves         :   41 ( 358 expanded)
%              Depth                    :   22
%              Number of atoms          : 1654 (17000 expanded)
%              Number of equality atoms :  133 (1016 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
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
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['19','22'])).

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

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['19','22'])).

thf('43',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','56'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('61',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('63',plain,
    ( ( ~ ( m1_subset_1 @ ( k7_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('65',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('77',plain,(
    ! [X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('81',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 != k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ( X38 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('85',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X37 @ k1_xboole_0 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('87',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('89',plain,(
    ! [X37: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X37 @ k1_xboole_0 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','87','88'])).

thf('90',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('102',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('103',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','110'])).

thf('112',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('113',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('114',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('115',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('116',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('117',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('118',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('119',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','107'])).

thf('121',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('125',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('127',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['123','127'])).

thf('129',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','70','112','113','114','115','116','117','118','119','128'])).

thf('130',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('131',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['129','130'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','132'])).

thf('134',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('135',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('137',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('149',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('155',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['153','156'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('158',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('161',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('163',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','163'])).

thf('165',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['142','164'])).

thf('166',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','165'])).

thf('167',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','141'])).

thf('168',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['153','156'])).

thf('169',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('172',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('173',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['167','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['166','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Au4t8JCzP
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:32:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 40.51/40.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 40.51/40.72  % Solved by: fo/fo7.sh
% 40.51/40.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 40.51/40.72  % done 21889 iterations in 40.255s
% 40.51/40.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 40.51/40.72  % SZS output start Refutation
% 40.51/40.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 40.51/40.72  thf(sk_C_type, type, sk_C: $i).
% 40.51/40.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 40.51/40.72  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 40.51/40.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 40.51/40.72  thf(sk_A_type, type, sk_A: $i).
% 40.51/40.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 40.51/40.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 40.51/40.72  thf(sk_B_type, type, sk_B: $i).
% 40.51/40.72  thf(sk_D_type, type, sk_D: $i).
% 40.51/40.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 40.51/40.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 40.51/40.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 40.51/40.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 40.51/40.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 40.51/40.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 40.51/40.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 40.51/40.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 40.51/40.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 40.51/40.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 40.51/40.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 40.51/40.72  thf(t38_funct_2, conjecture,
% 40.51/40.72    (![A:$i,B:$i,C:$i,D:$i]:
% 40.51/40.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 40.51/40.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 40.51/40.72       ( ( r1_tarski @ C @ A ) =>
% 40.51/40.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 40.51/40.72           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 40.51/40.72             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 40.51/40.72             ( m1_subset_1 @
% 40.51/40.72               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 40.51/40.72               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 40.51/40.72  thf(zf_stmt_0, negated_conjecture,
% 40.51/40.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 40.51/40.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 40.51/40.72            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 40.51/40.72          ( ( r1_tarski @ C @ A ) =>
% 40.51/40.72            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 40.51/40.72              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 40.51/40.72                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 40.51/40.72                ( m1_subset_1 @
% 40.51/40.72                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 40.51/40.72                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 40.51/40.72    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 40.51/40.72  thf('0', plain,
% 40.51/40.72      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 40.51/40.72        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 40.51/40.72             sk_B)
% 40.51/40.72        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('1', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf(dt_k2_partfun1, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i,D:$i]:
% 40.51/40.72     ( ( ( v1_funct_1 @ C ) & 
% 40.51/40.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 40.51/40.72       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 40.51/40.72         ( m1_subset_1 @
% 40.51/40.72           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 40.51/40.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 40.51/40.72  thf('2', plain,
% 40.51/40.72      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 40.51/40.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 40.51/40.72          | ~ (v1_funct_1 @ X39)
% 40.51/40.72          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 40.51/40.72      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 40.51/40.72  thf('3', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 40.51/40.72          | ~ (v1_funct_1 @ sk_D))),
% 40.51/40.72      inference('sup-', [status(thm)], ['1', '2'])).
% 40.51/40.72  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('5', plain,
% 40.51/40.72      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['3', '4'])).
% 40.51/40.72  thf('6', plain,
% 40.51/40.72      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 40.51/40.72        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 40.51/40.72      inference('demod', [status(thm)], ['0', '5'])).
% 40.51/40.72  thf('7', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf(redefinition_k2_partfun1, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i,D:$i]:
% 40.51/40.72     ( ( ( v1_funct_1 @ C ) & 
% 40.51/40.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 40.51/40.72       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 40.51/40.72  thf('8', plain,
% 40.51/40.72      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 40.51/40.72         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 40.51/40.72          | ~ (v1_funct_1 @ X43)
% 40.51/40.72          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 40.51/40.72      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 40.51/40.72  thf('9', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 40.51/40.72          | ~ (v1_funct_1 @ sk_D))),
% 40.51/40.72      inference('sup-', [status(thm)], ['7', '8'])).
% 40.51/40.72  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('11', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['9', '10'])).
% 40.51/40.72  thf('12', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['9', '10'])).
% 40.51/40.72  thf('13', plain,
% 40.51/40.72      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 40.51/40.72        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 40.51/40.72      inference('demod', [status(thm)], ['6', '11', '12'])).
% 40.51/40.72  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('15', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf(cc2_relset_1, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i]:
% 40.51/40.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 40.51/40.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 40.51/40.72  thf('16', plain,
% 40.51/40.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 40.51/40.72         ((v5_relat_1 @ X25 @ X27)
% 40.51/40.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 40.51/40.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 40.51/40.72  thf('17', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 40.51/40.72      inference('sup-', [status(thm)], ['15', '16'])).
% 40.51/40.72  thf(d19_relat_1, axiom,
% 40.51/40.72    (![A:$i,B:$i]:
% 40.51/40.72     ( ( v1_relat_1 @ B ) =>
% 40.51/40.72       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 40.51/40.72  thf('18', plain,
% 40.51/40.72      (![X13 : $i, X14 : $i]:
% 40.51/40.72         (~ (v5_relat_1 @ X13 @ X14)
% 40.51/40.72          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 40.51/40.72          | ~ (v1_relat_1 @ X13))),
% 40.51/40.72      inference('cnf', [status(esa)], [d19_relat_1])).
% 40.51/40.72  thf('19', plain,
% 40.51/40.72      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 40.51/40.72      inference('sup-', [status(thm)], ['17', '18'])).
% 40.51/40.72  thf('20', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf(cc1_relset_1, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i]:
% 40.51/40.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 40.51/40.72       ( v1_relat_1 @ C ) ))).
% 40.51/40.72  thf('21', plain,
% 40.51/40.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 40.51/40.72         ((v1_relat_1 @ X22)
% 40.51/40.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 40.51/40.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 40.51/40.72  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 40.51/40.72      inference('sup-', [status(thm)], ['20', '21'])).
% 40.51/40.72  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 40.51/40.72      inference('demod', [status(thm)], ['19', '22'])).
% 40.51/40.72  thf(d1_funct_2, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i]:
% 40.51/40.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 40.51/40.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 40.51/40.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 40.51/40.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 40.51/40.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 40.51/40.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 40.51/40.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 40.51/40.72  thf(zf_stmt_1, axiom,
% 40.51/40.72    (![B:$i,A:$i]:
% 40.51/40.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 40.51/40.72       ( zip_tseitin_0 @ B @ A ) ))).
% 40.51/40.72  thf('24', plain,
% 40.51/40.72      (![X31 : $i, X32 : $i]:
% 40.51/40.72         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 40.51/40.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 40.51/40.72  thf('25', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 40.51/40.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 40.51/40.72  thf('26', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.51/40.72         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 40.51/40.72      inference('sup+', [status(thm)], ['24', '25'])).
% 40.51/40.72  thf(d10_xboole_0, axiom,
% 40.51/40.72    (![A:$i,B:$i]:
% 40.51/40.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 40.51/40.72  thf('27', plain,
% 40.51/40.72      (![X0 : $i, X2 : $i]:
% 40.51/40.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 40.51/40.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 40.51/40.72  thf('28', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.51/40.72         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['26', '27'])).
% 40.51/40.72  thf('29', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['23', '28'])).
% 40.51/40.72  thf('30', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 40.51/40.72  thf(zf_stmt_3, axiom,
% 40.51/40.72    (![C:$i,B:$i,A:$i]:
% 40.51/40.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 40.51/40.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 40.51/40.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 40.51/40.72  thf(zf_stmt_5, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i]:
% 40.51/40.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 40.51/40.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 40.51/40.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 40.51/40.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 40.51/40.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 40.51/40.72  thf('31', plain,
% 40.51/40.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 40.51/40.72         (~ (zip_tseitin_0 @ X36 @ X37)
% 40.51/40.72          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 40.51/40.72          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 40.51/40.72  thf('32', plain,
% 40.51/40.72      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 40.51/40.72      inference('sup-', [status(thm)], ['30', '31'])).
% 40.51/40.72  thf('33', plain,
% 40.51/40.72      ((((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 40.51/40.72      inference('sup-', [status(thm)], ['29', '32'])).
% 40.51/40.72  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('35', plain,
% 40.51/40.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 40.51/40.72         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 40.51/40.72          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 40.51/40.72          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 40.51/40.72  thf('36', plain,
% 40.51/40.72      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 40.51/40.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['34', '35'])).
% 40.51/40.72  thf('37', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf(redefinition_k1_relset_1, axiom,
% 40.51/40.72    (![A:$i,B:$i,C:$i]:
% 40.51/40.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 40.51/40.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 40.51/40.72  thf('38', plain,
% 40.51/40.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 40.51/40.72         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 40.51/40.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 40.51/40.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 40.51/40.72  thf('39', plain,
% 40.51/40.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 40.51/40.72      inference('sup-', [status(thm)], ['37', '38'])).
% 40.51/40.72  thf('40', plain,
% 40.51/40.72      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 40.51/40.72      inference('demod', [status(thm)], ['36', '39'])).
% 40.51/40.72  thf('41', plain,
% 40.51/40.72      ((((k2_relat_1 @ sk_D) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['33', '40'])).
% 40.51/40.72  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 40.51/40.72      inference('demod', [status(thm)], ['19', '22'])).
% 40.51/40.72  thf('43', plain,
% 40.51/40.72      (![X31 : $i, X32 : $i]:
% 40.51/40.72         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 40.51/40.72  thf('44', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 40.51/40.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 40.51/40.72  thf('45', plain,
% 40.51/40.72      (![X0 : $i, X2 : $i]:
% 40.51/40.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 40.51/40.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 40.51/40.72  thf('46', plain,
% 40.51/40.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['44', '45'])).
% 40.51/40.72  thf('47', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.51/40.72         (~ (r1_tarski @ X1 @ X0)
% 40.51/40.72          | (zip_tseitin_0 @ X0 @ X2)
% 40.51/40.72          | ((X1) = (k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['43', '46'])).
% 40.51/40.72  thf('48', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['42', '47'])).
% 40.51/40.72  thf('49', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((sk_B) = (k1_xboole_0))
% 40.51/40.72          | ((sk_A) = (k1_relat_1 @ sk_D))
% 40.51/40.72          | (zip_tseitin_0 @ sk_B @ X0))),
% 40.51/40.72      inference('sup+', [status(thm)], ['41', '48'])).
% 40.51/40.72  thf('50', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('51', plain,
% 40.51/40.72      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 40.51/40.72      inference('split', [status(esa)], ['50'])).
% 40.51/40.72  thf('52', plain,
% 40.51/40.72      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('split', [status(esa)], ['50'])).
% 40.51/40.72  thf('53', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('54', plain,
% 40.51/40.72      (((m1_subset_1 @ sk_D @ 
% 40.51/40.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 40.51/40.72         <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup+', [status(thm)], ['52', '53'])).
% 40.51/40.72  thf(t113_zfmisc_1, axiom,
% 40.51/40.72    (![A:$i,B:$i]:
% 40.51/40.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 40.51/40.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 40.51/40.72  thf('55', plain,
% 40.51/40.72      (![X8 : $i, X9 : $i]:
% 40.51/40.72         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 40.51/40.72  thf('56', plain,
% 40.51/40.72      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 40.51/40.72      inference('simplify', [status(thm)], ['55'])).
% 40.51/40.72  thf('57', plain,
% 40.51/40.72      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 40.51/40.72         <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('demod', [status(thm)], ['54', '56'])).
% 40.51/40.72  thf(t3_subset, axiom,
% 40.51/40.72    (![A:$i,B:$i]:
% 40.51/40.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 40.51/40.72  thf('58', plain,
% 40.51/40.72      (![X10 : $i, X11 : $i]:
% 40.51/40.72         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 40.51/40.72      inference('cnf', [status(esa)], [t3_subset])).
% 40.51/40.72  thf('59', plain,
% 40.51/40.72      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup-', [status(thm)], ['57', '58'])).
% 40.51/40.72  thf('60', plain,
% 40.51/40.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['44', '45'])).
% 40.51/40.72  thf('61', plain,
% 40.51/40.72      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup-', [status(thm)], ['59', '60'])).
% 40.51/40.72  thf('62', plain,
% 40.51/40.72      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 40.51/40.72        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 40.51/40.72      inference('demod', [status(thm)], ['6', '11', '12'])).
% 40.51/40.72  thf('63', plain,
% 40.51/40.72      (((~ (m1_subset_1 @ (k7_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 40.51/40.72            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 40.51/40.72         | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)))
% 40.51/40.72         <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup-', [status(thm)], ['61', '62'])).
% 40.51/40.72  thf('64', plain,
% 40.51/40.72      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('split', [status(esa)], ['50'])).
% 40.51/40.72  thf('65', plain, ((r1_tarski @ sk_C @ sk_A)),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('66', plain,
% 40.51/40.72      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup+', [status(thm)], ['64', '65'])).
% 40.51/40.72  thf('67', plain,
% 40.51/40.72      (![X0 : $i, X2 : $i]:
% 40.51/40.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 40.51/40.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 40.51/40.72  thf('68', plain,
% 40.51/40.72      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 40.51/40.72         <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup-', [status(thm)], ['66', '67'])).
% 40.51/40.72  thf('69', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 40.51/40.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 40.51/40.72  thf('70', plain,
% 40.51/40.72      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('demod', [status(thm)], ['68', '69'])).
% 40.51/40.72  thf('71', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 40.51/40.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 40.51/40.72  thf('72', plain,
% 40.51/40.72      (![X10 : $i, X12 : $i]:
% 40.51/40.72         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 40.51/40.72      inference('cnf', [status(esa)], [t3_subset])).
% 40.51/40.72  thf('73', plain,
% 40.51/40.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['71', '72'])).
% 40.51/40.72  thf('74', plain,
% 40.51/40.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 40.51/40.72         ((v1_relat_1 @ X22)
% 40.51/40.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 40.51/40.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 40.51/40.72  thf('75', plain, ((v1_relat_1 @ k1_xboole_0)),
% 40.51/40.72      inference('sup-', [status(thm)], ['73', '74'])).
% 40.51/40.72  thf('76', plain,
% 40.51/40.72      (![X31 : $i, X32 : $i]:
% 40.51/40.72         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 40.51/40.72  thf(t110_relat_1, axiom,
% 40.51/40.72    (![A:$i]:
% 40.51/40.72     ( ( v1_relat_1 @ A ) =>
% 40.51/40.72       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 40.51/40.72  thf('77', plain,
% 40.51/40.72      (![X17 : $i]:
% 40.51/40.72         (((k7_relat_1 @ X17 @ k1_xboole_0) = (k1_xboole_0))
% 40.51/40.72          | ~ (v1_relat_1 @ X17))),
% 40.51/40.72      inference('cnf', [status(esa)], [t110_relat_1])).
% 40.51/40.72  thf('78', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.51/40.72         (((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 40.51/40.72          | (zip_tseitin_0 @ X0 @ X2)
% 40.51/40.72          | ~ (v1_relat_1 @ X1))),
% 40.51/40.72      inference('sup+', [status(thm)], ['76', '77'])).
% 40.51/40.72  thf('79', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         ((zip_tseitin_0 @ X1 @ X0)
% 40.51/40.72          | ((k7_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['75', '78'])).
% 40.51/40.72  thf('80', plain,
% 40.51/40.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['71', '72'])).
% 40.51/40.72  thf('81', plain,
% 40.51/40.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 40.51/40.72         (~ (zip_tseitin_0 @ X36 @ X37)
% 40.51/40.72          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 40.51/40.72          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 40.51/40.72  thf('82', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 40.51/40.72      inference('sup-', [status(thm)], ['80', '81'])).
% 40.51/40.72  thf('83', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         (((k7_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 40.51/40.72          | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['79', '82'])).
% 40.51/40.72  thf('84', plain,
% 40.51/40.72      (![X36 : $i, X37 : $i, X38 : $i]:
% 40.51/40.72         (((X36) != (k1_xboole_0))
% 40.51/40.72          | ((X37) = (k1_xboole_0))
% 40.51/40.72          | (v1_funct_2 @ X38 @ X37 @ X36)
% 40.51/40.72          | ((X38) != (k1_xboole_0))
% 40.51/40.72          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 40.51/40.72  thf('85', plain,
% 40.51/40.72      (![X37 : $i]:
% 40.51/40.72         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ k1_xboole_0)))
% 40.51/40.72          | (v1_funct_2 @ k1_xboole_0 @ X37 @ k1_xboole_0)
% 40.51/40.72          | ((X37) = (k1_xboole_0)))),
% 40.51/40.72      inference('simplify', [status(thm)], ['84'])).
% 40.51/40.72  thf('86', plain,
% 40.51/40.72      (![X8 : $i, X9 : $i]:
% 40.51/40.72         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 40.51/40.72  thf('87', plain,
% 40.51/40.72      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 40.51/40.72      inference('simplify', [status(thm)], ['86'])).
% 40.51/40.72  thf('88', plain,
% 40.51/40.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['71', '72'])).
% 40.51/40.72  thf('89', plain,
% 40.51/40.72      (![X37 : $i]:
% 40.51/40.72         ((v1_funct_2 @ k1_xboole_0 @ X37 @ k1_xboole_0)
% 40.51/40.72          | ((X37) = (k1_xboole_0)))),
% 40.51/40.72      inference('demod', [status(thm)], ['85', '87', '88'])).
% 40.51/40.72  thf('90', plain,
% 40.51/40.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 40.51/40.72         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 40.51/40.72          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 40.51/40.72          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 40.51/40.72  thf('91', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((X0) = (k1_xboole_0))
% 40.51/40.72          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 40.51/40.72          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['89', '90'])).
% 40.51/40.72  thf('92', plain,
% 40.51/40.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['71', '72'])).
% 40.51/40.72  thf('93', plain,
% 40.51/40.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 40.51/40.72         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 40.51/40.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 40.51/40.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 40.51/40.72  thf('94', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['92', '93'])).
% 40.51/40.72  thf('95', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 40.51/40.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 40.51/40.72  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 40.51/40.72      inference('simplify', [status(thm)], ['95'])).
% 40.51/40.72  thf('97', plain,
% 40.51/40.72      (![X10 : $i, X12 : $i]:
% 40.51/40.72         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 40.51/40.72      inference('cnf', [status(esa)], [t3_subset])).
% 40.51/40.72  thf('98', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['96', '97'])).
% 40.51/40.72  thf('99', plain,
% 40.51/40.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 40.51/40.72         ((v1_relat_1 @ X22)
% 40.51/40.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 40.51/40.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 40.51/40.72  thf('100', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['98', '99'])).
% 40.51/40.72  thf('101', plain,
% 40.51/40.72      (![X17 : $i]:
% 40.51/40.72         (((k7_relat_1 @ X17 @ k1_xboole_0) = (k1_xboole_0))
% 40.51/40.72          | ~ (v1_relat_1 @ X17))),
% 40.51/40.72      inference('cnf', [status(esa)], [t110_relat_1])).
% 40.51/40.72  thf('102', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 40.51/40.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 40.51/40.72  thf(t91_relat_1, axiom,
% 40.51/40.72    (![A:$i,B:$i]:
% 40.51/40.72     ( ( v1_relat_1 @ B ) =>
% 40.51/40.72       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 40.51/40.72         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 40.51/40.72  thf('103', plain,
% 40.51/40.72      (![X18 : $i, X19 : $i]:
% 40.51/40.72         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 40.51/40.72          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 40.51/40.72          | ~ (v1_relat_1 @ X19))),
% 40.51/40.72      inference('cnf', [status(esa)], [t91_relat_1])).
% 40.51/40.72  thf('104', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (v1_relat_1 @ X0)
% 40.51/40.72          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['102', '103'])).
% 40.51/40.72  thf('105', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 40.51/40.72          | ~ (v1_relat_1 @ X0)
% 40.51/40.72          | ~ (v1_relat_1 @ X0))),
% 40.51/40.72      inference('sup+', [status(thm)], ['101', '104'])).
% 40.51/40.72  thf('106', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (v1_relat_1 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 40.51/40.72      inference('simplify', [status(thm)], ['105'])).
% 40.51/40.72  thf('107', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['100', '106'])).
% 40.51/40.72  thf('108', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.51/40.72      inference('demod', [status(thm)], ['94', '107'])).
% 40.51/40.72  thf('109', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((X0) = (k1_xboole_0))
% 40.51/40.72          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 40.51/40.72          | ((X0) = (k1_xboole_0)))),
% 40.51/40.72      inference('demod', [status(thm)], ['91', '108'])).
% 40.51/40.72  thf('110', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 40.51/40.72          | ((X0) = (k1_xboole_0)))),
% 40.51/40.72      inference('simplify', [status(thm)], ['109'])).
% 40.51/40.72  thf('111', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 40.51/40.72          | ((X0) = (k1_xboole_0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['83', '110'])).
% 40.51/40.72  thf('112', plain,
% 40.51/40.72      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.51/40.72      inference('condensation', [status(thm)], ['111'])).
% 40.51/40.72  thf('113', plain,
% 40.51/40.72      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('demod', [status(thm)], ['68', '69'])).
% 40.51/40.72  thf('114', plain,
% 40.51/40.72      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 40.51/40.72      inference('simplify', [status(thm)], ['55'])).
% 40.51/40.72  thf('115', plain,
% 40.51/40.72      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['71', '72'])).
% 40.51/40.72  thf('116', plain,
% 40.51/40.72      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('sup-', [status(thm)], ['59', '60'])).
% 40.51/40.72  thf('117', plain,
% 40.51/40.72      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('demod', [status(thm)], ['68', '69'])).
% 40.51/40.72  thf('118', plain,
% 40.51/40.72      (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.51/40.72      inference('condensation', [status(thm)], ['111'])).
% 40.51/40.72  thf('119', plain,
% 40.51/40.72      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 40.51/40.72      inference('demod', [status(thm)], ['68', '69'])).
% 40.51/40.72  thf('120', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.51/40.72      inference('demod', [status(thm)], ['94', '107'])).
% 40.51/40.72  thf('121', plain,
% 40.51/40.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 40.51/40.72         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 40.51/40.72          | (v1_funct_2 @ X35 @ X33 @ X34)
% 40.51/40.72          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 40.51/40.72  thf('122', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         (((X1) != (k1_xboole_0))
% 40.51/40.72          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 40.51/40.72          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['120', '121'])).
% 40.51/40.72  thf('123', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 40.51/40.72          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 40.51/40.72      inference('simplify', [status(thm)], ['122'])).
% 40.51/40.72  thf('124', plain,
% 40.51/40.72      (![X31 : $i, X32 : $i]:
% 40.51/40.72         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 40.51/40.72  thf('125', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 40.51/40.72      inference('simplify', [status(thm)], ['124'])).
% 40.51/40.72  thf('126', plain,
% 40.51/40.72      (![X0 : $i, X1 : $i]:
% 40.51/40.72         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 40.51/40.72      inference('sup-', [status(thm)], ['80', '81'])).
% 40.51/40.72  thf('127', plain,
% 40.51/40.72      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 40.51/40.72      inference('sup-', [status(thm)], ['125', '126'])).
% 40.51/40.72  thf('128', plain,
% 40.51/40.72      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 40.51/40.72      inference('demod', [status(thm)], ['123', '127'])).
% 40.51/40.72  thf('129', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 40.51/40.72      inference('demod', [status(thm)],
% 40.51/40.72                ['63', '70', '112', '113', '114', '115', '116', '117', '118', 
% 40.51/40.72                 '119', '128'])).
% 40.51/40.72  thf('130', plain,
% 40.51/40.72      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 40.51/40.72      inference('split', [status(esa)], ['50'])).
% 40.51/40.72  thf('131', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 40.51/40.72      inference('sat_resolution*', [status(thm)], ['129', '130'])).
% 40.51/40.72  thf('132', plain, (((sk_B) != (k1_xboole_0))),
% 40.51/40.72      inference('simpl_trail', [status(thm)], ['51', '131'])).
% 40.51/40.72  thf('133', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 40.51/40.72      inference('simplify_reflect-', [status(thm)], ['49', '132'])).
% 40.51/40.72  thf('134', plain,
% 40.51/40.72      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 40.51/40.72      inference('sup-', [status(thm)], ['30', '31'])).
% 40.51/40.72  thf('135', plain,
% 40.51/40.72      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 40.51/40.72      inference('sup-', [status(thm)], ['133', '134'])).
% 40.51/40.72  thf('136', plain,
% 40.51/40.72      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 40.51/40.72      inference('demod', [status(thm)], ['36', '39'])).
% 40.51/40.72  thf('137', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 40.51/40.72      inference('clc', [status(thm)], ['135', '136'])).
% 40.51/40.72  thf('138', plain,
% 40.51/40.72      (![X18 : $i, X19 : $i]:
% 40.51/40.72         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 40.51/40.72          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 40.51/40.72          | ~ (v1_relat_1 @ X19))),
% 40.51/40.72      inference('cnf', [status(esa)], [t91_relat_1])).
% 40.51/40.72  thf('139', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (r1_tarski @ X0 @ sk_A)
% 40.51/40.72          | ~ (v1_relat_1 @ sk_D)
% 40.51/40.72          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 40.51/40.72      inference('sup-', [status(thm)], ['137', '138'])).
% 40.51/40.72  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 40.51/40.72      inference('sup-', [status(thm)], ['20', '21'])).
% 40.51/40.72  thf('141', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (r1_tarski @ X0 @ sk_A)
% 40.51/40.72          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 40.51/40.72      inference('demod', [status(thm)], ['139', '140'])).
% 40.51/40.72  thf('142', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 40.51/40.72      inference('sup-', [status(thm)], ['14', '141'])).
% 40.51/40.72  thf('143', plain,
% 40.51/40.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('144', plain,
% 40.51/40.72      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 40.51/40.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 40.51/40.72          | ~ (v1_funct_1 @ X39)
% 40.51/40.72          | (m1_subset_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42) @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 40.51/40.72      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 40.51/40.72  thf('145', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 40.51/40.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 40.51/40.72          | ~ (v1_funct_1 @ sk_D))),
% 40.51/40.72      inference('sup-', [status(thm)], ['143', '144'])).
% 40.51/40.72  thf('146', plain, ((v1_funct_1 @ sk_D)),
% 40.51/40.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.51/40.72  thf('147', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 40.51/40.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('demod', [status(thm)], ['145', '146'])).
% 40.51/40.72  thf('148', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['9', '10'])).
% 40.51/40.72  thf('149', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 40.51/40.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('demod', [status(thm)], ['147', '148'])).
% 40.51/40.72  thf('150', plain,
% 40.51/40.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 40.51/40.72         ((v5_relat_1 @ X25 @ X27)
% 40.51/40.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 40.51/40.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 40.51/40.72  thf('151', plain,
% 40.51/40.72      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 40.51/40.72      inference('sup-', [status(thm)], ['149', '150'])).
% 40.51/40.72  thf('152', plain,
% 40.51/40.72      (![X13 : $i, X14 : $i]:
% 40.51/40.72         (~ (v5_relat_1 @ X13 @ X14)
% 40.51/40.72          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 40.51/40.72          | ~ (v1_relat_1 @ X13))),
% 40.51/40.72      inference('cnf', [status(esa)], [d19_relat_1])).
% 40.51/40.72  thf('153', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 40.51/40.72          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 40.51/40.72      inference('sup-', [status(thm)], ['151', '152'])).
% 40.51/40.72  thf('154', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 40.51/40.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 40.51/40.72      inference('demod', [status(thm)], ['147', '148'])).
% 40.51/40.72  thf('155', plain,
% 40.51/40.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 40.51/40.72         ((v1_relat_1 @ X22)
% 40.51/40.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 40.51/40.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 40.51/40.72  thf('156', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['154', '155'])).
% 40.51/40.72  thf('157', plain,
% 40.51/40.72      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 40.51/40.72      inference('demod', [status(thm)], ['153', '156'])).
% 40.51/40.72  thf(t4_funct_2, axiom,
% 40.51/40.72    (![A:$i,B:$i]:
% 40.51/40.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 40.51/40.72       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 40.51/40.72         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 40.51/40.72           ( m1_subset_1 @
% 40.51/40.72             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 40.51/40.72  thf('158', plain,
% 40.51/40.72      (![X47 : $i, X48 : $i]:
% 40.51/40.72         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 40.51/40.72          | (v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ X48)
% 40.51/40.72          | ~ (v1_funct_1 @ X47)
% 40.51/40.72          | ~ (v1_relat_1 @ X47))),
% 40.51/40.72      inference('cnf', [status(esa)], [t4_funct_2])).
% 40.51/40.72  thf('159', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 40.51/40.72          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 40.51/40.72          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 40.51/40.72             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 40.51/40.72      inference('sup-', [status(thm)], ['157', '158'])).
% 40.51/40.72  thf('160', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['154', '155'])).
% 40.51/40.72  thf('161', plain,
% 40.51/40.72      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['3', '4'])).
% 40.51/40.72  thf('162', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['9', '10'])).
% 40.51/40.72  thf('163', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['161', '162'])).
% 40.51/40.72  thf('164', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 40.51/40.72          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 40.51/40.72      inference('demod', [status(thm)], ['159', '160', '163'])).
% 40.51/40.72  thf('165', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 40.51/40.72      inference('sup+', [status(thm)], ['142', '164'])).
% 40.51/40.72  thf('166', plain,
% 40.51/40.72      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 40.51/40.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 40.51/40.72      inference('demod', [status(thm)], ['13', '165'])).
% 40.51/40.72  thf('167', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 40.51/40.72      inference('sup-', [status(thm)], ['14', '141'])).
% 40.51/40.72  thf('168', plain,
% 40.51/40.72      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 40.51/40.72      inference('demod', [status(thm)], ['153', '156'])).
% 40.51/40.72  thf('169', plain,
% 40.51/40.72      (![X47 : $i, X48 : $i]:
% 40.51/40.72         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 40.51/40.72          | (m1_subset_1 @ X47 @ 
% 40.51/40.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ X48)))
% 40.51/40.72          | ~ (v1_funct_1 @ X47)
% 40.51/40.72          | ~ (v1_relat_1 @ X47))),
% 40.51/40.72      inference('cnf', [status(esa)], [t4_funct_2])).
% 40.51/40.72  thf('170', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 40.51/40.72          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 40.51/40.72          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 40.51/40.72             (k1_zfmisc_1 @ 
% 40.51/40.72              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 40.51/40.72      inference('sup-', [status(thm)], ['168', '169'])).
% 40.51/40.72  thf('171', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('sup-', [status(thm)], ['154', '155'])).
% 40.51/40.72  thf('172', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 40.51/40.72      inference('demod', [status(thm)], ['161', '162'])).
% 40.51/40.72  thf('173', plain,
% 40.51/40.72      (![X0 : $i]:
% 40.51/40.72         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 40.51/40.72          (k1_zfmisc_1 @ 
% 40.51/40.72           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 40.51/40.72      inference('demod', [status(thm)], ['170', '171', '172'])).
% 40.51/40.72  thf('174', plain,
% 40.51/40.72      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 40.51/40.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 40.51/40.72      inference('sup+', [status(thm)], ['167', '173'])).
% 40.51/40.72  thf('175', plain, ($false), inference('demod', [status(thm)], ['166', '174'])).
% 40.51/40.72  
% 40.51/40.72  % SZS output end Refutation
% 40.51/40.72  
% 40.53/40.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
