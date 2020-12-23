%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xihzq2Ucj6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:06 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  170 (2078 expanded)
%              Number of leaves         :   37 ( 606 expanded)
%              Depth                    :   24
%              Number of atoms          : 1127 (28842 expanded)
%              Number of equality atoms :   91 (1545 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['14','17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','25','26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

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

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('76',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['72','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('94',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','94'])).

thf('96',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','25','26'])).

thf('97',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','97'])).

thf('99',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('100',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','100'])).

thf('102',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','101'])).

thf('103',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','102'])).

thf('104',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','103'])).

thf('105',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('109',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','109'])).

thf('111',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','109'])).

thf('118',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('119',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('121',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','109'])).

thf('122',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('123',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['116','117','119','120','121','122'])).

thf('124',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','102'])).

thf('126',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['116','117','119','120','121','122'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('129',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['72','78'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['111','123','129','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xihzq2Ucj6
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 343 iterations in 0.207s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.66  thf(t8_funct_2, conjecture,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.45/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.66           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.45/0.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.45/0.66            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.66              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.45/0.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_D)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.45/0.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.45/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.45/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.66  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['5', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.66         ((v4_relat_1 @ X15 @ X16)
% 0.45/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.66  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf(d18_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         (~ (v4_relat_1 @ X10 @ X11)
% 0.45/0.66          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.45/0.66          | ~ (v1_relat_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc1_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( v1_relat_1 @ C ) ))).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.66         ((v1_relat_1 @ X12)
% 0.45/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.66  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['14', '17'])).
% 0.45/0.66  thf(t11_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ C ) =>
% 0.45/0.66       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.45/0.66           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.45/0.66          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.45/0.66          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.45/0.66          | ~ (v1_relat_1 @ X24))),
% 0.45/0.66      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ sk_D)
% 0.45/0.66          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.66          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.66  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.66          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.45/0.66         <= (~
% 0.45/0.66             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.45/0.66       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.45/0.66       ~ ((v1_funct_1 @ sk_D))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('27', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.45/0.66  thf('28', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.45/0.66  thf(d1_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_1, axiom,
% 0.45/0.66    (![B:$i,A:$i]:
% 0.45/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '22'])).
% 0.45/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_3, axiom,
% 0.45/0.66    (![C:$i,B:$i,A:$i]:
% 0.45/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_5, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.66         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.45/0.66          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.45/0.66          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '32'])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '22'])).
% 0.45/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.45/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.66  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.66         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.45/0.66          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.45/0.66          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.45/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.45/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.45/0.66      inference('demod', [status(thm)], ['39', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.66         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.45/0.66          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.45/0.66          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['44', '47'])).
% 0.45/0.66  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.45/0.66      inference('split', [status(esa)], ['49'])).
% 0.45/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.66  thf('51', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf(t3_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (![X7 : $i, X9 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.45/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.66         ((v4_relat_1 @ X15 @ X16)
% 0.45/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.66  thf('58', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.45/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         (~ (v4_relat_1 @ X10 @ X11)
% 0.45/0.66          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.45/0.66          | ~ (v1_relat_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.66          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.66         ((v1_relat_1 @ X12)
% 0.45/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.66  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.66  thf('64', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.45/0.66      inference('demod', [status(thm)], ['60', '63'])).
% 0.45/0.66  thf('65', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '68'])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.66         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.45/0.66          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.45/0.66          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((X1) != (k1_xboole_0))
% 0.45/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.45/0.66          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.66          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf('74', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.45/0.66      inference('simplify', [status(thm)], ['73'])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.66         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.45/0.66          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.45/0.66          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.66  thf('78', plain,
% 0.45/0.66      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['74', '77'])).
% 0.45/0.66  thf('79', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.66      inference('demod', [status(thm)], ['72', '78'])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('split', [status(esa)], ['49'])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.45/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.45/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf(t113_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['83'])).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('split', [status(esa)], ['49'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_D @ 
% 0.45/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.45/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['85', '86'])).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.45/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['84', '87'])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 0.45/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.66  thf('93', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('95', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.45/0.66         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('demod', [status(thm)], ['82', '94'])).
% 0.45/0.66  thf('96', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.45/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['95', '96'])).
% 0.45/0.66  thf('98', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['79', '97'])).
% 0.45/0.66  thf('99', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('split', [status(esa)], ['49'])).
% 0.45/0.66  thf('100', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.45/0.66  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['50', '100'])).
% 0.45/0.66  thf('102', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['48', '101'])).
% 0.45/0.66  thf('103', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '102'])).
% 0.45/0.66  thf('104', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['36', '103'])).
% 0.45/0.66  thf('105', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.66         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.45/0.66          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.45/0.66          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('106', plain,
% 0.45/0.66      ((((sk_A) != (sk_A))
% 0.45/0.66        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.45/0.66        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['104', '105'])).
% 0.45/0.66  thf('107', plain,
% 0.45/0.66      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.45/0.66        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.45/0.66      inference('simplify', [status(thm)], ['106'])).
% 0.45/0.66  thf('108', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.45/0.66  thf('109', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.45/0.66      inference('clc', [status(thm)], ['107', '108'])).
% 0.45/0.66  thf('110', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '109'])).
% 0.45/0.66  thf('111', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.45/0.66      inference('demod', [status(thm)], ['28', '110'])).
% 0.45/0.66  thf('112', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '22'])).
% 0.45/0.66  thf('113', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('114', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.66  thf('115', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('116', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.45/0.66        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.66  thf('117', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '109'])).
% 0.45/0.66  thf('118', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.66  thf('119', plain,
% 0.45/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['118'])).
% 0.45/0.66  thf('120', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf('121', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '109'])).
% 0.45/0.66  thf('122', plain,
% 0.45/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['118'])).
% 0.45/0.66  thf('123', plain, (((k1_xboole_0) = (sk_D))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['116', '117', '119', '120', '121', '122'])).
% 0.45/0.66  thf('124', plain,
% 0.45/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.66  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '102'])).
% 0.45/0.66  thf('126', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.66  thf('127', plain, (((k1_xboole_0) = (sk_D))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['116', '117', '119', '120', '121', '122'])).
% 0.45/0.66  thf('128', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '68'])).
% 0.45/0.66  thf('129', plain, (((k1_xboole_0) = (sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.45/0.66  thf('130', plain,
% 0.45/0.66      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.66      inference('demod', [status(thm)], ['72', '78'])).
% 0.45/0.66  thf('131', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['111', '123', '129', '130'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
