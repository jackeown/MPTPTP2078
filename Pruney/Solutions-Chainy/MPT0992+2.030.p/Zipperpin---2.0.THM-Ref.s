%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GoESAQN3cF

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:38 EST 2020

% Result     : Theorem 25.74s
% Output     : Refutation 25.74s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 995 expanded)
%              Number of leaves         :   41 ( 306 expanded)
%              Depth                    :   22
%              Number of atoms          : 1553 (16184 expanded)
%              Number of equality atoms :  124 ( 962 expanded)
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

thf('53',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('54',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

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
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('68',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('82',plain,(
    ! [X17: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('87',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('89',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('90',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('92',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('94',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X17: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('97',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('98',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('103',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','104'])).

thf('106',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('112',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['108','114'])).

thf('116',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['54','66','73','84','85','86','87','88','89','90','91','92','115'])).

thf('117',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('118',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','119'])).

thf('121',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('122',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('136',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('142',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['140','143'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('145',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('150',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['146','147','150'])).

thf('152',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['129','151'])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','152'])).

thf('154',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','128'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['140','143'])).

thf('156',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X47 ) @ X48 )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('159',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('160',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['154','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['153','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GoESAQN3cF
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 25.74/25.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 25.74/25.96  % Solved by: fo/fo7.sh
% 25.74/25.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.74/25.96  % done 16587 iterations in 25.498s
% 25.74/25.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 25.74/25.96  % SZS output start Refutation
% 25.74/25.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 25.74/25.96  thf(sk_C_type, type, sk_C: $i).
% 25.74/25.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 25.74/25.96  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 25.74/25.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 25.74/25.96  thf(sk_A_type, type, sk_A: $i).
% 25.74/25.96  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 25.74/25.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 25.74/25.96  thf(sk_B_type, type, sk_B: $i).
% 25.74/25.96  thf(sk_D_type, type, sk_D: $i).
% 25.74/25.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 25.74/25.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 25.74/25.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 25.74/25.96  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 25.74/25.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 25.74/25.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 25.74/25.96  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 25.74/25.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 25.74/25.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 25.74/25.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 25.74/25.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 25.74/25.96  thf(t38_funct_2, conjecture,
% 25.74/25.96    (![A:$i,B:$i,C:$i,D:$i]:
% 25.74/25.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 25.74/25.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.74/25.96       ( ( r1_tarski @ C @ A ) =>
% 25.74/25.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 25.74/25.96           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 25.74/25.96             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 25.74/25.96             ( m1_subset_1 @
% 25.74/25.96               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 25.74/25.96               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 25.74/25.96  thf(zf_stmt_0, negated_conjecture,
% 25.74/25.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 25.74/25.96        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 25.74/25.96            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.74/25.96          ( ( r1_tarski @ C @ A ) =>
% 25.74/25.96            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 25.74/25.96              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 25.74/25.96                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 25.74/25.96                ( m1_subset_1 @
% 25.74/25.96                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 25.74/25.96                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 25.74/25.96    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 25.74/25.96  thf('0', plain,
% 25.74/25.96      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 25.74/25.96        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 25.74/25.96             sk_B)
% 25.74/25.96        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 25.74/25.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('1', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf(dt_k2_partfun1, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i,D:$i]:
% 25.74/25.96     ( ( ( v1_funct_1 @ C ) & 
% 25.74/25.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.74/25.96       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 25.74/25.96         ( m1_subset_1 @
% 25.74/25.96           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 25.74/25.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 25.74/25.96  thf('2', plain,
% 25.74/25.96      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 25.74/25.96         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 25.74/25.96          | ~ (v1_funct_1 @ X39)
% 25.74/25.96          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 25.74/25.96      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 25.74/25.96  thf('3', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 25.74/25.96          | ~ (v1_funct_1 @ sk_D))),
% 25.74/25.96      inference('sup-', [status(thm)], ['1', '2'])).
% 25.74/25.96  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('5', plain,
% 25.74/25.96      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['3', '4'])).
% 25.74/25.96  thf('6', plain,
% 25.74/25.96      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 25.74/25.96        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 25.74/25.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 25.74/25.96      inference('demod', [status(thm)], ['0', '5'])).
% 25.74/25.96  thf('7', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf(redefinition_k2_partfun1, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i,D:$i]:
% 25.74/25.96     ( ( ( v1_funct_1 @ C ) & 
% 25.74/25.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 25.74/25.96       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 25.74/25.96  thf('8', plain,
% 25.74/25.96      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 25.74/25.96         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 25.74/25.96          | ~ (v1_funct_1 @ X43)
% 25.74/25.96          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 25.74/25.96      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 25.74/25.96  thf('9', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 25.74/25.96          | ~ (v1_funct_1 @ sk_D))),
% 25.74/25.96      inference('sup-', [status(thm)], ['7', '8'])).
% 25.74/25.96  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('11', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['9', '10'])).
% 25.74/25.96  thf('12', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['9', '10'])).
% 25.74/25.96  thf('13', plain,
% 25.74/25.96      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 25.74/25.96        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 25.74/25.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 25.74/25.96      inference('demod', [status(thm)], ['6', '11', '12'])).
% 25.74/25.96  thf('14', plain, ((r1_tarski @ sk_C @ sk_A)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('15', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf(cc2_relset_1, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i]:
% 25.74/25.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.74/25.96       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 25.74/25.96  thf('16', plain,
% 25.74/25.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 25.74/25.96         ((v5_relat_1 @ X25 @ X27)
% 25.74/25.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 25.74/25.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 25.74/25.96  thf('17', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 25.74/25.96      inference('sup-', [status(thm)], ['15', '16'])).
% 25.74/25.96  thf(d19_relat_1, axiom,
% 25.74/25.96    (![A:$i,B:$i]:
% 25.74/25.96     ( ( v1_relat_1 @ B ) =>
% 25.74/25.96       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 25.74/25.96  thf('18', plain,
% 25.74/25.96      (![X13 : $i, X14 : $i]:
% 25.74/25.96         (~ (v5_relat_1 @ X13 @ X14)
% 25.74/25.96          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 25.74/25.96          | ~ (v1_relat_1 @ X13))),
% 25.74/25.96      inference('cnf', [status(esa)], [d19_relat_1])).
% 25.74/25.96  thf('19', plain,
% 25.74/25.96      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 25.74/25.96      inference('sup-', [status(thm)], ['17', '18'])).
% 25.74/25.96  thf('20', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf(cc1_relset_1, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i]:
% 25.74/25.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.74/25.96       ( v1_relat_1 @ C ) ))).
% 25.74/25.96  thf('21', plain,
% 25.74/25.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 25.74/25.96         ((v1_relat_1 @ X22)
% 25.74/25.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 25.74/25.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 25.74/25.96  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 25.74/25.96      inference('sup-', [status(thm)], ['20', '21'])).
% 25.74/25.96  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 25.74/25.96      inference('demod', [status(thm)], ['19', '22'])).
% 25.74/25.96  thf(d1_funct_2, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i]:
% 25.74/25.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.74/25.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 25.74/25.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 25.74/25.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 25.74/25.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 25.74/25.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 25.74/25.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 25.74/25.96  thf(zf_stmt_1, axiom,
% 25.74/25.96    (![B:$i,A:$i]:
% 25.74/25.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 25.74/25.96       ( zip_tseitin_0 @ B @ A ) ))).
% 25.74/25.96  thf('24', plain,
% 25.74/25.96      (![X31 : $i, X32 : $i]:
% 25.74/25.96         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.74/25.96  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 25.74/25.96  thf('25', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 25.74/25.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.74/25.96  thf('26', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 25.74/25.96      inference('sup+', [status(thm)], ['24', '25'])).
% 25.74/25.96  thf(d10_xboole_0, axiom,
% 25.74/25.96    (![A:$i,B:$i]:
% 25.74/25.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 25.74/25.96  thf('27', plain,
% 25.74/25.96      (![X0 : $i, X2 : $i]:
% 25.74/25.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 25.74/25.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.74/25.96  thf('28', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['26', '27'])).
% 25.74/25.96  thf('29', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['23', '28'])).
% 25.74/25.96  thf('30', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 25.74/25.96  thf(zf_stmt_3, axiom,
% 25.74/25.96    (![C:$i,B:$i,A:$i]:
% 25.74/25.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 25.74/25.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 25.74/25.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 25.74/25.96  thf(zf_stmt_5, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i]:
% 25.74/25.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.74/25.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 25.74/25.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 25.74/25.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 25.74/25.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 25.74/25.96  thf('31', plain,
% 25.74/25.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 25.74/25.96         (~ (zip_tseitin_0 @ X36 @ X37)
% 25.74/25.96          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 25.74/25.96          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.74/25.96  thf('32', plain,
% 25.74/25.96      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 25.74/25.96      inference('sup-', [status(thm)], ['30', '31'])).
% 25.74/25.96  thf('33', plain,
% 25.74/25.96      ((((k2_relat_1 @ sk_D) = (sk_B)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 25.74/25.96      inference('sup-', [status(thm)], ['29', '32'])).
% 25.74/25.96  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('35', plain,
% 25.74/25.96      (![X33 : $i, X34 : $i, X35 : $i]:
% 25.74/25.96         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 25.74/25.96          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 25.74/25.96          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 25.74/25.96  thf('36', plain,
% 25.74/25.96      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 25.74/25.96        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['34', '35'])).
% 25.74/25.96  thf('37', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf(redefinition_k1_relset_1, axiom,
% 25.74/25.96    (![A:$i,B:$i,C:$i]:
% 25.74/25.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 25.74/25.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 25.74/25.96  thf('38', plain,
% 25.74/25.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 25.74/25.96         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 25.74/25.96          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 25.74/25.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.74/25.96  thf('39', plain,
% 25.74/25.96      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 25.74/25.96      inference('sup-', [status(thm)], ['37', '38'])).
% 25.74/25.96  thf('40', plain,
% 25.74/25.96      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 25.74/25.96      inference('demod', [status(thm)], ['36', '39'])).
% 25.74/25.96  thf('41', plain,
% 25.74/25.96      ((((k2_relat_1 @ sk_D) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['33', '40'])).
% 25.74/25.96  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 25.74/25.96      inference('demod', [status(thm)], ['19', '22'])).
% 25.74/25.96  thf('43', plain,
% 25.74/25.96      (![X31 : $i, X32 : $i]:
% 25.74/25.96         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.74/25.96  thf('44', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 25.74/25.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.74/25.96  thf('45', plain,
% 25.74/25.96      (![X0 : $i, X2 : $i]:
% 25.74/25.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 25.74/25.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.74/25.96  thf('46', plain,
% 25.74/25.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['44', '45'])).
% 25.74/25.96  thf('47', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96         (~ (r1_tarski @ X1 @ X0)
% 25.74/25.96          | (zip_tseitin_0 @ X0 @ X2)
% 25.74/25.96          | ((X1) = (k1_xboole_0)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['43', '46'])).
% 25.74/25.96  thf('48', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['42', '47'])).
% 25.74/25.96  thf('49', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (((sk_B) = (k1_xboole_0))
% 25.74/25.96          | ((sk_A) = (k1_relat_1 @ sk_D))
% 25.74/25.96          | (zip_tseitin_0 @ sk_B @ X0))),
% 25.74/25.96      inference('sup+', [status(thm)], ['41', '48'])).
% 25.74/25.96  thf('50', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('51', plain,
% 25.74/25.96      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 25.74/25.96      inference('split', [status(esa)], ['50'])).
% 25.74/25.96  thf('52', plain,
% 25.74/25.96      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('split', [status(esa)], ['50'])).
% 25.74/25.96  thf('53', plain,
% 25.74/25.96      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 25.74/25.96        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 25.74/25.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 25.74/25.96      inference('demod', [status(thm)], ['0', '5'])).
% 25.74/25.96  thf('54', plain,
% 25.74/25.96      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 25.74/25.96            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 25.74/25.96         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 25.74/25.96              sk_B)))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['52', '53'])).
% 25.74/25.96  thf(t113_zfmisc_1, axiom,
% 25.74/25.96    (![A:$i,B:$i]:
% 25.74/25.96     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 25.74/25.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 25.74/25.96  thf('55', plain,
% 25.74/25.96      (![X8 : $i, X9 : $i]:
% 25.74/25.96         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 25.74/25.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 25.74/25.96  thf('56', plain,
% 25.74/25.96      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 25.74/25.96      inference('simplify', [status(thm)], ['55'])).
% 25.74/25.96  thf('57', plain,
% 25.74/25.96      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('split', [status(esa)], ['50'])).
% 25.74/25.96  thf('58', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('59', plain,
% 25.74/25.96      (((m1_subset_1 @ sk_D @ 
% 25.74/25.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup+', [status(thm)], ['57', '58'])).
% 25.74/25.96  thf('60', plain,
% 25.74/25.96      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup+', [status(thm)], ['56', '59'])).
% 25.74/25.96  thf(t3_subset, axiom,
% 25.74/25.96    (![A:$i,B:$i]:
% 25.74/25.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 25.74/25.96  thf('61', plain,
% 25.74/25.96      (![X10 : $i, X11 : $i]:
% 25.74/25.96         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 25.74/25.96      inference('cnf', [status(esa)], [t3_subset])).
% 25.74/25.96  thf('62', plain,
% 25.74/25.96      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['60', '61'])).
% 25.74/25.96  thf('63', plain,
% 25.74/25.96      (![X0 : $i, X2 : $i]:
% 25.74/25.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 25.74/25.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.74/25.96  thf('64', plain,
% 25.74/25.96      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['62', '63'])).
% 25.74/25.96  thf('65', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 25.74/25.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.74/25.96  thf('66', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['64', '65'])).
% 25.74/25.96  thf('67', plain,
% 25.74/25.96      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('split', [status(esa)], ['50'])).
% 25.74/25.96  thf('68', plain, ((r1_tarski @ sk_C @ sk_A)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('69', plain,
% 25.74/25.96      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup+', [status(thm)], ['67', '68'])).
% 25.74/25.96  thf('70', plain,
% 25.74/25.96      (![X0 : $i, X2 : $i]:
% 25.74/25.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 25.74/25.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 25.74/25.96  thf('71', plain,
% 25.74/25.96      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['69', '70'])).
% 25.74/25.96  thf('72', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 25.74/25.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.74/25.96  thf('73', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['71', '72'])).
% 25.74/25.96  thf('74', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['64', '65'])).
% 25.74/25.96  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('76', plain,
% 25.74/25.96      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup+', [status(thm)], ['74', '75'])).
% 25.74/25.96  thf('77', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 25.74/25.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.74/25.96  thf('78', plain,
% 25.74/25.96      (![X10 : $i, X12 : $i]:
% 25.74/25.96         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 25.74/25.96      inference('cnf', [status(esa)], [t3_subset])).
% 25.74/25.96  thf('79', plain,
% 25.74/25.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['77', '78'])).
% 25.74/25.96  thf('80', plain,
% 25.74/25.96      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 25.74/25.96         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 25.74/25.96          | ~ (v1_funct_1 @ X43)
% 25.74/25.96          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 25.74/25.96      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 25.74/25.96  thf('81', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 25.74/25.96            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 25.74/25.96          | ~ (v1_funct_1 @ k1_xboole_0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['79', '80'])).
% 25.74/25.96  thf(t111_relat_1, axiom,
% 25.74/25.96    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 25.74/25.96  thf('82', plain,
% 25.74/25.96      (![X17 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 25.74/25.96      inference('cnf', [status(esa)], [t111_relat_1])).
% 25.74/25.96  thf('83', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 25.74/25.96          | ~ (v1_funct_1 @ k1_xboole_0))),
% 25.74/25.96      inference('demod', [status(thm)], ['81', '82'])).
% 25.74/25.96  thf('84', plain,
% 25.74/25.96      ((![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['76', '83'])).
% 25.74/25.96  thf('85', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['71', '72'])).
% 25.74/25.96  thf('86', plain,
% 25.74/25.96      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 25.74/25.96      inference('simplify', [status(thm)], ['55'])).
% 25.74/25.96  thf('87', plain,
% 25.74/25.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['77', '78'])).
% 25.74/25.96  thf('88', plain,
% 25.74/25.96      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('split', [status(esa)], ['50'])).
% 25.74/25.96  thf('89', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['64', '65'])).
% 25.74/25.96  thf('90', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['71', '72'])).
% 25.74/25.96  thf('91', plain,
% 25.74/25.96      ((![X0 : $i, X1 : $i, X2 : $i]:
% 25.74/25.96          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 25.74/25.96         <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['76', '83'])).
% 25.74/25.96  thf('92', plain,
% 25.74/25.96      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 25.74/25.96      inference('demod', [status(thm)], ['71', '72'])).
% 25.74/25.96  thf('93', plain,
% 25.74/25.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['77', '78'])).
% 25.74/25.96  thf('94', plain,
% 25.74/25.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 25.74/25.96         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 25.74/25.96          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 25.74/25.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 25.74/25.96  thf('95', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i]:
% 25.74/25.96         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['93', '94'])).
% 25.74/25.96  thf('96', plain,
% 25.74/25.96      (![X17 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 25.74/25.96      inference('cnf', [status(esa)], [t111_relat_1])).
% 25.74/25.96  thf('97', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 25.74/25.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 25.74/25.96  thf(t91_relat_1, axiom,
% 25.74/25.96    (![A:$i,B:$i]:
% 25.74/25.96     ( ( v1_relat_1 @ B ) =>
% 25.74/25.96       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 25.74/25.96         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 25.74/25.96  thf('98', plain,
% 25.74/25.96      (![X18 : $i, X19 : $i]:
% 25.74/25.96         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 25.74/25.96          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 25.74/25.96          | ~ (v1_relat_1 @ X19))),
% 25.74/25.96      inference('cnf', [status(esa)], [t91_relat_1])).
% 25.74/25.96  thf('99', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (~ (v1_relat_1 @ X0)
% 25.74/25.96          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['97', '98'])).
% 25.74/25.96  thf('100', plain,
% 25.74/25.96      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 25.74/25.96        | ~ (v1_relat_1 @ k1_xboole_0))),
% 25.74/25.96      inference('sup+', [status(thm)], ['96', '99'])).
% 25.74/25.96  thf('101', plain,
% 25.74/25.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['77', '78'])).
% 25.74/25.96  thf('102', plain,
% 25.74/25.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 25.74/25.96         ((v1_relat_1 @ X22)
% 25.74/25.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 25.74/25.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 25.74/25.96  thf('103', plain, ((v1_relat_1 @ k1_xboole_0)),
% 25.74/25.96      inference('sup-', [status(thm)], ['101', '102'])).
% 25.74/25.96  thf('104', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 25.74/25.96      inference('demod', [status(thm)], ['100', '103'])).
% 25.74/25.96  thf('105', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i]:
% 25.74/25.96         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 25.74/25.96      inference('demod', [status(thm)], ['95', '104'])).
% 25.74/25.96  thf('106', plain,
% 25.74/25.96      (![X33 : $i, X34 : $i, X35 : $i]:
% 25.74/25.96         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 25.74/25.96          | (v1_funct_2 @ X35 @ X33 @ X34)
% 25.74/25.96          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 25.74/25.96  thf('107', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i]:
% 25.74/25.96         (((X1) != (k1_xboole_0))
% 25.74/25.96          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 25.74/25.96          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['105', '106'])).
% 25.74/25.96  thf('108', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 25.74/25.96          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 25.74/25.96      inference('simplify', [status(thm)], ['107'])).
% 25.74/25.96  thf('109', plain,
% 25.74/25.96      (![X31 : $i, X32 : $i]:
% 25.74/25.96         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 25.74/25.96  thf('110', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 25.74/25.96      inference('simplify', [status(thm)], ['109'])).
% 25.74/25.96  thf('111', plain,
% 25.74/25.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['77', '78'])).
% 25.74/25.96  thf('112', plain,
% 25.74/25.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 25.74/25.96         (~ (zip_tseitin_0 @ X36 @ X37)
% 25.74/25.96          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 25.74/25.96          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 25.74/25.96  thf('113', plain,
% 25.74/25.96      (![X0 : $i, X1 : $i]:
% 25.74/25.96         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 25.74/25.96      inference('sup-', [status(thm)], ['111', '112'])).
% 25.74/25.96  thf('114', plain,
% 25.74/25.96      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 25.74/25.96      inference('sup-', [status(thm)], ['110', '113'])).
% 25.74/25.96  thf('115', plain,
% 25.74/25.96      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 25.74/25.96      inference('demod', [status(thm)], ['108', '114'])).
% 25.74/25.96  thf('116', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 25.74/25.96      inference('demod', [status(thm)],
% 25.74/25.96                ['54', '66', '73', '84', '85', '86', '87', '88', '89', '90', 
% 25.74/25.96                 '91', '92', '115'])).
% 25.74/25.96  thf('117', plain,
% 25.74/25.96      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 25.74/25.96      inference('split', [status(esa)], ['50'])).
% 25.74/25.96  thf('118', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 25.74/25.96      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 25.74/25.96  thf('119', plain, (((sk_B) != (k1_xboole_0))),
% 25.74/25.96      inference('simpl_trail', [status(thm)], ['51', '118'])).
% 25.74/25.96  thf('120', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ sk_B @ X0))),
% 25.74/25.96      inference('simplify_reflect-', [status(thm)], ['49', '119'])).
% 25.74/25.96  thf('121', plain,
% 25.74/25.96      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 25.74/25.96      inference('sup-', [status(thm)], ['30', '31'])).
% 25.74/25.96  thf('122', plain,
% 25.74/25.96      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 25.74/25.96      inference('sup-', [status(thm)], ['120', '121'])).
% 25.74/25.96  thf('123', plain,
% 25.74/25.96      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 25.74/25.96      inference('demod', [status(thm)], ['36', '39'])).
% 25.74/25.96  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 25.74/25.96      inference('clc', [status(thm)], ['122', '123'])).
% 25.74/25.96  thf('125', plain,
% 25.74/25.96      (![X18 : $i, X19 : $i]:
% 25.74/25.96         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 25.74/25.96          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 25.74/25.96          | ~ (v1_relat_1 @ X19))),
% 25.74/25.96      inference('cnf', [status(esa)], [t91_relat_1])).
% 25.74/25.96  thf('126', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (~ (r1_tarski @ X0 @ sk_A)
% 25.74/25.96          | ~ (v1_relat_1 @ sk_D)
% 25.74/25.96          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 25.74/25.96      inference('sup-', [status(thm)], ['124', '125'])).
% 25.74/25.96  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 25.74/25.96      inference('sup-', [status(thm)], ['20', '21'])).
% 25.74/25.96  thf('128', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (~ (r1_tarski @ X0 @ sk_A)
% 25.74/25.96          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 25.74/25.96      inference('demod', [status(thm)], ['126', '127'])).
% 25.74/25.96  thf('129', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 25.74/25.96      inference('sup-', [status(thm)], ['14', '128'])).
% 25.74/25.96  thf('130', plain,
% 25.74/25.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('131', plain,
% 25.74/25.96      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 25.74/25.96         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 25.74/25.96          | ~ (v1_funct_1 @ X39)
% 25.74/25.96          | (m1_subset_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42) @ 
% 25.74/25.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 25.74/25.96      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 25.74/25.96  thf('132', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 25.74/25.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 25.74/25.96          | ~ (v1_funct_1 @ sk_D))),
% 25.74/25.96      inference('sup-', [status(thm)], ['130', '131'])).
% 25.74/25.96  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 25.74/25.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.74/25.96  thf('134', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 25.74/25.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('demod', [status(thm)], ['132', '133'])).
% 25.74/25.96  thf('135', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['9', '10'])).
% 25.74/25.96  thf('136', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 25.74/25.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('demod', [status(thm)], ['134', '135'])).
% 25.74/25.96  thf('137', plain,
% 25.74/25.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 25.74/25.96         ((v5_relat_1 @ X25 @ X27)
% 25.74/25.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 25.74/25.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 25.74/25.96  thf('138', plain,
% 25.74/25.96      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 25.74/25.96      inference('sup-', [status(thm)], ['136', '137'])).
% 25.74/25.96  thf('139', plain,
% 25.74/25.96      (![X13 : $i, X14 : $i]:
% 25.74/25.96         (~ (v5_relat_1 @ X13 @ X14)
% 25.74/25.96          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 25.74/25.96          | ~ (v1_relat_1 @ X13))),
% 25.74/25.96      inference('cnf', [status(esa)], [d19_relat_1])).
% 25.74/25.96  thf('140', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 25.74/25.96          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 25.74/25.96      inference('sup-', [status(thm)], ['138', '139'])).
% 25.74/25.96  thf('141', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 25.74/25.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 25.74/25.96      inference('demod', [status(thm)], ['134', '135'])).
% 25.74/25.96  thf('142', plain,
% 25.74/25.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 25.74/25.96         ((v1_relat_1 @ X22)
% 25.74/25.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 25.74/25.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 25.74/25.96  thf('143', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['141', '142'])).
% 25.74/25.96  thf('144', plain,
% 25.74/25.96      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 25.74/25.96      inference('demod', [status(thm)], ['140', '143'])).
% 25.74/25.96  thf(t4_funct_2, axiom,
% 25.74/25.96    (![A:$i,B:$i]:
% 25.74/25.96     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 25.74/25.96       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 25.74/25.96         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 25.74/25.96           ( m1_subset_1 @
% 25.74/25.96             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 25.74/25.96  thf('145', plain,
% 25.74/25.96      (![X47 : $i, X48 : $i]:
% 25.74/25.96         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 25.74/25.96          | (v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ X48)
% 25.74/25.96          | ~ (v1_funct_1 @ X47)
% 25.74/25.96          | ~ (v1_relat_1 @ X47))),
% 25.74/25.96      inference('cnf', [status(esa)], [t4_funct_2])).
% 25.74/25.96  thf('146', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 25.74/25.96          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 25.74/25.96          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 25.74/25.96             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 25.74/25.96      inference('sup-', [status(thm)], ['144', '145'])).
% 25.74/25.96  thf('147', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['141', '142'])).
% 25.74/25.96  thf('148', plain,
% 25.74/25.96      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['3', '4'])).
% 25.74/25.96  thf('149', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['9', '10'])).
% 25.74/25.96  thf('150', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['148', '149'])).
% 25.74/25.96  thf('151', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 25.74/25.96          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 25.74/25.96      inference('demod', [status(thm)], ['146', '147', '150'])).
% 25.74/25.96  thf('152', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 25.74/25.96      inference('sup+', [status(thm)], ['129', '151'])).
% 25.74/25.96  thf('153', plain,
% 25.74/25.96      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 25.74/25.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 25.74/25.96      inference('demod', [status(thm)], ['13', '152'])).
% 25.74/25.96  thf('154', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 25.74/25.96      inference('sup-', [status(thm)], ['14', '128'])).
% 25.74/25.96  thf('155', plain,
% 25.74/25.96      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 25.74/25.96      inference('demod', [status(thm)], ['140', '143'])).
% 25.74/25.96  thf('156', plain,
% 25.74/25.96      (![X47 : $i, X48 : $i]:
% 25.74/25.96         (~ (r1_tarski @ (k2_relat_1 @ X47) @ X48)
% 25.74/25.96          | (m1_subset_1 @ X47 @ 
% 25.74/25.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ X48)))
% 25.74/25.96          | ~ (v1_funct_1 @ X47)
% 25.74/25.96          | ~ (v1_relat_1 @ X47))),
% 25.74/25.96      inference('cnf', [status(esa)], [t4_funct_2])).
% 25.74/25.96  thf('157', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 25.74/25.96          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 25.74/25.96          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 25.74/25.96             (k1_zfmisc_1 @ 
% 25.74/25.96              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 25.74/25.96      inference('sup-', [status(thm)], ['155', '156'])).
% 25.74/25.96  thf('158', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('sup-', [status(thm)], ['141', '142'])).
% 25.74/25.96  thf('159', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 25.74/25.96      inference('demod', [status(thm)], ['148', '149'])).
% 25.74/25.96  thf('160', plain,
% 25.74/25.96      (![X0 : $i]:
% 25.74/25.96         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 25.74/25.96          (k1_zfmisc_1 @ 
% 25.74/25.96           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 25.74/25.96      inference('demod', [status(thm)], ['157', '158', '159'])).
% 25.74/25.96  thf('161', plain,
% 25.74/25.96      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 25.74/25.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 25.74/25.96      inference('sup+', [status(thm)], ['154', '160'])).
% 25.74/25.96  thf('162', plain, ($false), inference('demod', [status(thm)], ['153', '161'])).
% 25.74/25.96  
% 25.74/25.96  % SZS output end Refutation
% 25.74/25.96  
% 25.74/25.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
