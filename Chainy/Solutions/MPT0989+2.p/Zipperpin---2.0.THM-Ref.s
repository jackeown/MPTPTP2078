%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0989+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rI8cVKC5oN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 54.90s
% Output     : Refutation 54.90s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 170 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  699 (2382 expanded)
%              Number of equality atoms :   76 ( 247 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_98_type,type,(
    sk_B_98: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_98_type,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(zip_tseitin_97_type,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t35_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
     => ( ( ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ ( C @ ( k2_funct_1 @ C ) ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C @ C ) )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
              = B )
            & ( v2_funct_1 @ C ) )
         => ( ( B = k1_xboole_0 )
            | ( ( ( k5_relat_1 @ ( C @ ( k2_funct_1 @ C ) ) )
                = ( k6_partfun1 @ A ) )
              & ( ( k5_relat_1 @ ( k2_funct_1 @ C @ C ) )
                = ( k6_partfun1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_funct_2])).

thf('0',plain,
    ( ( ( k5_relat_1 @ ( sk_C_110 @ ( k2_funct_1 @ sk_C_110 ) ) )
     != ( k6_partfun1 @ sk_A_16 ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k5_relat_1 @ ( sk_C_110 @ ( k2_funct_1 @ sk_C_110 ) ) )
     != ( k6_partfun1 @ sk_A_16 ) )
   <= ( ( k5_relat_1 @ ( sk_C_110 @ ( k2_funct_1 @ sk_C_110 ) ) )
     != ( k6_partfun1 @ sk_A_16 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) )
    | ( v1_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C_110 ),
    inference(demod,[status(thm)],['4','5'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X2668: $i] :
      ( ~ ( v2_funct_1 @ X2668 )
      | ( ( k2_funct_1 @ X2668 )
        = ( k4_relat_1 @ X2668 ) )
      | ~ ( v1_funct_1 @ X2668 )
      | ~ ( v1_relat_1 @ X2668 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C_110 )
    | ( ( k2_funct_1 @ sk_C_110 )
      = ( k4_relat_1 @ sk_C_110 ) )
    | ~ ( v2_funct_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_1 @ sk_C_110 )
    = ( k4_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( k2_funct_1 @ sk_C_110 )
    = ( k4_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ ( A @ ( k2_funct_1 @ A ) ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A @ A ) )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X3002: $i] :
      ( ~ ( v2_funct_1 @ X3002 )
      | ( ( k5_relat_1 @ ( X3002 @ ( k2_funct_1 @ X3002 ) ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3002 ) ) )
      | ~ ( v1_funct_1 @ X3002 )
      | ~ ( v1_relat_1 @ X3002 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X4697: $i] :
      ( ( k6_partfun1 @ X4697 )
      = ( k6_relat_1 @ X4697 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X3002: $i] :
      ( ~ ( v2_funct_1 @ X3002 )
      | ( ( k5_relat_1 @ ( X3002 @ ( k2_funct_1 @ X3002 ) ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X3002 ) ) )
      | ~ ( v1_funct_1 @ X3002 )
      | ~ ( v1_relat_1 @ X3002 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k5_relat_1 @ ( sk_C_110 @ ( k4_relat_1 @ sk_C_110 ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C_110 ) ) )
    | ~ ( v1_relat_1 @ sk_C_110 )
    | ~ ( v1_funct_1 @ sk_C_110 )
    | ~ ( v2_funct_1 @ sk_C_110 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_110 ),
    inference(demod,[status(thm)],['4','5'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k5_relat_1 @ ( sk_C_110 @ ( k4_relat_1 @ sk_C_110 ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C_110 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_A_16 ) )
   <= ( ( k5_relat_1 @ ( sk_C_110 @ ( k2_funct_1 @ sk_C_110 ) ) )
     != ( k6_partfun1 @ sk_A_16 ) ) ),
    inference(demod,[status(thm)],['1','11','20'])).

thf('22',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X3598: $i,X3599: $i,X3600: $i] :
      ( ( ( k2_relset_1 @ ( X3599 @ ( X3600 @ X3598 ) ) )
        = ( k2_relat_1 @ X3598 ) )
      | ~ ( m1_subset_1 @ ( X3598 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3599 @ X3600 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = ( k2_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = sk_B_98 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C_110 )
    = sk_B_98 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3002: $i] :
      ( ~ ( v2_funct_1 @ X3002 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3002 @ X3002 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ X3002 ) ) )
      | ~ ( v1_funct_1 @ X3002 )
      | ~ ( v1_relat_1 @ X3002 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('28',plain,(
    ! [X4697: $i] :
      ( ( k6_partfun1 @ X4697 )
      = ( k6_relat_1 @ X4697 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X3002: $i] :
      ( ~ ( v2_funct_1 @ X3002 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3002 @ X3002 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X3002 ) ) )
      | ~ ( v1_funct_1 @ X3002 )
      | ~ ( v1_relat_1 @ X3002 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) )
   <= ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C_110 ) )
       != ( k6_partfun1 @ sk_B_98 ) )
      | ~ ( v1_relat_1 @ sk_C_110 )
      | ~ ( v1_funct_1 @ sk_C_110 )
      | ~ ( v2_funct_1 @ sk_C_110 ) )
   <= ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_110 ),
    inference(demod,[status(thm)],['4','5'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) )
   <= ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( ( k6_partfun1 @ sk_B_98 )
     != ( k6_partfun1 @ sk_B_98 ) )
   <= ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
    = ( k6_partfun1 @ sk_B_98 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k5_relat_1 @ ( sk_C_110 @ ( k2_funct_1 @ sk_C_110 ) ) )
     != ( k6_partfun1 @ sk_A_16 ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_110 @ sk_C_110 ) )
     != ( k6_partfun1 @ sk_B_98 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ( k5_relat_1 @ ( sk_C_110 @ ( k2_funct_1 @ sk_C_110 ) ) )
 != ( k6_partfun1 @ sk_A_16 ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k6_partfun1 @ ( k1_relat_1 @ sk_C_110 ) )
 != ( k6_partfun1 @ sk_A_16 ) ),
    inference(simpl_trail,[status(thm)],['21','39'])).

thf('41',plain,(
    v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_98 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          <=> ( A
              = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_98 @ ( C @ ( B @ A ) ) )
     => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
      <=> ( A
          = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X4644: $i,X4645: $i,X4646: $i] :
      ( ~ ( v1_funct_2 @ ( X4646 @ ( X4644 @ X4645 ) ) )
      | ( X4644
        = ( k1_relset_1 @ ( X4644 @ ( X4645 @ X4646 ) ) ) )
      | ~ ( zip_tseitin_98 @ ( X4646 @ ( X4645 @ X4644 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,
    ( ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) )
    | ( sk_A_16
      = ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X3595: $i,X3596: $i,X3597: $i] :
      ( ( ( k1_relset_1 @ ( X3596 @ ( X3597 @ X3595 ) ) )
        = ( k1_relat_1 @ X3595 ) )
      | ~ ( m1_subset_1 @ ( X3595 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3596 @ X3597 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) )
    | ( sk_A_16
      = ( k1_relat_1 @ sk_C_110 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_97 @ ( B @ A ) ) ) )).

thf('48',plain,(
    ! [X4642: $i,X4643: $i] :
      ( ( zip_tseitin_97 @ ( X4642 @ X4643 ) )
      | ( X4642 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    ! [X4642: $i,X4643: $i] :
      ( ( zip_tseitin_97 @ ( X4642 @ X4643 ) )
      | ( X4642 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( zip_tseitin_97 @ ( B @ A ) )
         => ( zip_tseitin_98 @ ( C @ ( B @ A ) ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X4647: $i,X4648: $i,X4649: $i] :
      ( ~ ( zip_tseitin_97 @ ( X4647 @ X4648 ) )
      | ( zip_tseitin_98 @ ( X4649 @ ( X4647 @ X4648 ) ) )
      | ~ ( m1_subset_1 @ ( X4649 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4648 @ X4647 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,
    ( ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) )
    | ~ ( zip_tseitin_97 @ ( sk_B_98 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B_98 = o_0_0_xboole_0 )
    | ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_B_98 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('57',plain,(
    sk_B_98 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

thf('59',plain,
    ( sk_A_16
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['47','58'])).

thf('60',plain,(
    ( k6_partfun1 @ sk_A_16 )
 != ( k6_partfun1 @ sk_A_16 ) ),
    inference(demod,[status(thm)],['40','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
