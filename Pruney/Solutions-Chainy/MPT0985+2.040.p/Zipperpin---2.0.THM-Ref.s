%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eTelSIiOtr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:32 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  210 (1797 expanded)
%              Number of leaves         :   46 ( 558 expanded)
%              Depth                    :   23
%              Number of atoms          : 1382 (26196 expanded)
%              Number of equality atoms :   89 (1087 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

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

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X46: $i] :
      ( ( v1_funct_2 @ X46 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('47',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('49',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('56',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('62',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','54','60','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','67'])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','72'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('86',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('87',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('88',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('92',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('93',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('98',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('99',plain,(
    ! [X11: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X11 ) )
      = ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('100',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('102',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','84','102'])).

thf('104',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('108',plain,(
    ! [X43: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X43 ) @ X43 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('109',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('110',plain,(
    ! [X43: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X43 ) @ X43 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('113',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('115',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','119'])).

thf('121',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['103','120'])).

thf('122',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('123',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','121','122'])).

thf('124',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','123'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('126',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('130',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('138',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','147'])).

thf('149',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('150',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('152',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','121','122'])).

thf('154',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['152','153'])).

thf('155',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','154'])).

thf('156',plain,(
    ! [X46: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('157',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('159',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('160',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('161',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['124','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eTelSIiOtr
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:28:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.18/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.38  % Solved by: fo/fo7.sh
% 1.18/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.38  % done 1274 iterations in 0.934s
% 1.18/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.38  % SZS output start Refutation
% 1.18/1.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.38  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.18/1.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.18/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.38  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.18/1.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.18/1.38  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.18/1.38  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.18/1.38  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.38  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.18/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.18/1.38  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.18/1.38  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.18/1.38  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.18/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.38  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.38  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.18/1.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.38  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.18/1.38  thf(t31_funct_2, conjecture,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.38       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.18/1.38         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.18/1.38           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.18/1.38           ( m1_subset_1 @
% 1.18/1.38             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.18/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.38    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.38        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.38            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.38          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.18/1.38            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.18/1.38              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.18/1.38              ( m1_subset_1 @
% 1.18/1.38                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.18/1.38    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.18/1.38  thf('0', plain,
% 1.18/1.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.18/1.38        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.18/1.38        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('1', plain,
% 1.18/1.38      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('split', [status(esa)], ['0'])).
% 1.18/1.38  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(d9_funct_1, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.38       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.18/1.38  thf('3', plain,
% 1.18/1.38      (![X12 : $i]:
% 1.18/1.38         (~ (v2_funct_1 @ X12)
% 1.18/1.38          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 1.18/1.38          | ~ (v1_funct_1 @ X12)
% 1.18/1.38          | ~ (v1_relat_1 @ X12))),
% 1.18/1.38      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.18/1.38  thf('4', plain,
% 1.18/1.38      ((~ (v1_relat_1 @ sk_C)
% 1.18/1.38        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.18/1.38        | ~ (v2_funct_1 @ sk_C))),
% 1.18/1.38      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.38  thf('5', plain,
% 1.18/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(cc1_relset_1, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.38       ( v1_relat_1 @ C ) ))).
% 1.18/1.38  thf('6', plain,
% 1.18/1.38      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.18/1.38         ((v1_relat_1 @ X17)
% 1.18/1.38          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.18/1.38      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.18/1.38  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf('10', plain,
% 1.18/1.38      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('demod', [status(thm)], ['1', '9'])).
% 1.18/1.38  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf(dt_k2_funct_1, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.38       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.18/1.38         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.18/1.38  thf('12', plain,
% 1.18/1.38      (![X13 : $i]:
% 1.18/1.38         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.18/1.38          | ~ (v1_funct_1 @ X13)
% 1.18/1.38          | ~ (v1_relat_1 @ X13))),
% 1.18/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.18/1.38  thf('13', plain,
% 1.18/1.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.18/1.38         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.18/1.38      inference('split', [status(esa)], ['0'])).
% 1.18/1.38  thf('14', plain,
% 1.18/1.38      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.18/1.38         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['12', '13'])).
% 1.18/1.38  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('16', plain,
% 1.18/1.38      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.18/1.38      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.38  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['11', '16'])).
% 1.18/1.38  thf('18', plain,
% 1.18/1.38      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('split', [status(esa)], ['0'])).
% 1.18/1.38  thf('19', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf(d1_funct_2, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.38       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.38           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.18/1.38             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.18/1.38         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.38           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.18/1.38             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.18/1.38  thf(zf_stmt_1, axiom,
% 1.18/1.38    (![B:$i,A:$i]:
% 1.18/1.38     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.38       ( zip_tseitin_0 @ B @ A ) ))).
% 1.18/1.38  thf('20', plain,
% 1.18/1.38      (![X35 : $i, X36 : $i]:
% 1.18/1.38         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.38  thf('21', plain,
% 1.18/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.18/1.38  thf(zf_stmt_3, axiom,
% 1.18/1.38    (![C:$i,B:$i,A:$i]:
% 1.18/1.38     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.18/1.38       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.38  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.18/1.38  thf(zf_stmt_5, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.38       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.18/1.38         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.38           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.18/1.38             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.18/1.38  thf('22', plain,
% 1.18/1.38      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.18/1.38         (~ (zip_tseitin_0 @ X40 @ X41)
% 1.18/1.38          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 1.18/1.38          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.38  thf('23', plain,
% 1.18/1.38      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.18/1.38      inference('sup-', [status(thm)], ['21', '22'])).
% 1.18/1.38  thf('24', plain,
% 1.18/1.38      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.18/1.38      inference('sup-', [status(thm)], ['20', '23'])).
% 1.18/1.38  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('26', plain,
% 1.18/1.38      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.18/1.38         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 1.18/1.38          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 1.18/1.38          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.18/1.38  thf('27', plain,
% 1.18/1.38      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.18/1.38        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['25', '26'])).
% 1.18/1.38  thf('28', plain,
% 1.18/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(redefinition_k1_relset_1, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.38       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.18/1.38  thf('29', plain,
% 1.18/1.38      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.18/1.38         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.18/1.38          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.18/1.38      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.38  thf('30', plain,
% 1.18/1.38      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.18/1.38      inference('sup-', [status(thm)], ['28', '29'])).
% 1.18/1.38  thf('31', plain,
% 1.18/1.38      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['27', '30'])).
% 1.18/1.38  thf('32', plain,
% 1.18/1.38      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['24', '31'])).
% 1.18/1.38  thf('33', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf(t55_funct_1, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.38       ( ( v2_funct_1 @ A ) =>
% 1.18/1.38         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.18/1.38           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.18/1.38  thf('34', plain,
% 1.18/1.38      (![X16 : $i]:
% 1.18/1.38         (~ (v2_funct_1 @ X16)
% 1.18/1.38          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.18/1.38          | ~ (v1_funct_1 @ X16)
% 1.18/1.38          | ~ (v1_relat_1 @ X16))),
% 1.18/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.18/1.38  thf('35', plain,
% 1.18/1.38      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.18/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.18/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.18/1.38        | ~ (v2_funct_1 @ sk_C))),
% 1.18/1.38      inference('sup+', [status(thm)], ['33', '34'])).
% 1.18/1.38  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('39', plain,
% 1.18/1.38      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.18/1.38  thf('40', plain,
% 1.18/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(redefinition_k2_relset_1, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.38       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.18/1.38  thf('41', plain,
% 1.18/1.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.18/1.38         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.18/1.38          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.18/1.38      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.38  thf('42', plain,
% 1.18/1.38      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.18/1.38      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.38  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.18/1.38      inference('sup+', [status(thm)], ['42', '43'])).
% 1.18/1.38  thf('45', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['39', '44'])).
% 1.18/1.38  thf(t3_funct_2, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.38       ( ( v1_funct_1 @ A ) & 
% 1.18/1.38         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.18/1.38         ( m1_subset_1 @
% 1.18/1.38           A @ 
% 1.18/1.38           ( k1_zfmisc_1 @
% 1.18/1.38             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.18/1.38  thf('46', plain,
% 1.18/1.38      (![X46 : $i]:
% 1.18/1.38         ((v1_funct_2 @ X46 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46))
% 1.18/1.38          | ~ (v1_funct_1 @ X46)
% 1.18/1.38          | ~ (v1_relat_1 @ X46))),
% 1.18/1.38      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.18/1.38  thf('47', plain,
% 1.18/1.38      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 1.18/1.38         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.18/1.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.18/1.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('sup+', [status(thm)], ['45', '46'])).
% 1.18/1.38  thf('48', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf('49', plain,
% 1.18/1.38      (![X16 : $i]:
% 1.18/1.38         (~ (v2_funct_1 @ X16)
% 1.18/1.38          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 1.18/1.38          | ~ (v1_funct_1 @ X16)
% 1.18/1.38          | ~ (v1_relat_1 @ X16))),
% 1.18/1.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.18/1.38  thf('50', plain,
% 1.18/1.38      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.18/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.18/1.38        | ~ (v1_funct_1 @ sk_C)
% 1.18/1.38        | ~ (v2_funct_1 @ sk_C))),
% 1.18/1.38      inference('sup+', [status(thm)], ['48', '49'])).
% 1.18/1.38  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('54', plain,
% 1.18/1.38      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.18/1.38  thf('55', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf('56', plain,
% 1.18/1.38      (![X13 : $i]:
% 1.18/1.38         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.18/1.38          | ~ (v1_funct_1 @ X13)
% 1.18/1.38          | ~ (v1_relat_1 @ X13))),
% 1.18/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.18/1.38  thf('57', plain,
% 1.18/1.38      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.18/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.18/1.38        | ~ (v1_funct_1 @ sk_C))),
% 1.18/1.38      inference('sup+', [status(thm)], ['55', '56'])).
% 1.18/1.38  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('60', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.18/1.38  thf('61', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf('62', plain,
% 1.18/1.38      (![X13 : $i]:
% 1.18/1.38         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.18/1.38          | ~ (v1_funct_1 @ X13)
% 1.18/1.38          | ~ (v1_relat_1 @ X13))),
% 1.18/1.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.18/1.38  thf('63', plain,
% 1.18/1.38      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 1.18/1.38        | ~ (v1_relat_1 @ sk_C)
% 1.18/1.38        | ~ (v1_funct_1 @ sk_C))),
% 1.18/1.38      inference('sup+', [status(thm)], ['61', '62'])).
% 1.18/1.38  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.18/1.38  thf('67', plain,
% 1.18/1.38      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['47', '54', '60', '66'])).
% 1.18/1.38  thf('68', plain,
% 1.18/1.38      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 1.18/1.38        | ((sk_B) = (k1_xboole_0)))),
% 1.18/1.38      inference('sup+', [status(thm)], ['32', '67'])).
% 1.18/1.38  thf('69', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf('70', plain,
% 1.18/1.38      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('split', [status(esa)], ['0'])).
% 1.18/1.38  thf('71', plain,
% 1.18/1.38      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['69', '70'])).
% 1.18/1.38  thf('72', plain,
% 1.18/1.38      ((((sk_B) = (k1_xboole_0)))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['68', '71'])).
% 1.18/1.38  thf('73', plain,
% 1.18/1.38      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('demod', [status(thm)], ['18', '19', '72'])).
% 1.18/1.38  thf('74', plain,
% 1.18/1.38      ((((sk_B) = (k1_xboole_0)))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['68', '71'])).
% 1.18/1.38  thf('75', plain,
% 1.18/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(cc4_relset_1, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ( v1_xboole_0 @ A ) =>
% 1.18/1.38       ( ![C:$i]:
% 1.18/1.38         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.18/1.38           ( v1_xboole_0 @ C ) ) ) ))).
% 1.18/1.38  thf('76', plain,
% 1.18/1.38      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.38         (~ (v1_xboole_0 @ X20)
% 1.18/1.38          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 1.18/1.38          | (v1_xboole_0 @ X21))),
% 1.18/1.38      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.18/1.38  thf('77', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 1.18/1.38      inference('sup-', [status(thm)], ['75', '76'])).
% 1.18/1.38  thf('78', plain,
% 1.18/1.38      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['74', '77'])).
% 1.18/1.38  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.18/1.38  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.38  thf('80', plain,
% 1.18/1.38      (((v1_xboole_0 @ sk_C))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('demod', [status(thm)], ['78', '79'])).
% 1.18/1.38  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.38  thf(t8_boole, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.18/1.38  thf('82', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.18/1.38      inference('cnf', [status(esa)], [t8_boole])).
% 1.18/1.38  thf('83', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.38  thf('84', plain,
% 1.18/1.38      ((((k1_xboole_0) = (sk_C)))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['80', '83'])).
% 1.18/1.38  thf(t113_zfmisc_1, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.18/1.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.18/1.38  thf('85', plain,
% 1.18/1.38      (![X3 : $i, X4 : $i]:
% 1.18/1.38         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.18/1.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.18/1.38  thf('86', plain,
% 1.18/1.38      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.18/1.38      inference('simplify', [status(thm)], ['85'])).
% 1.18/1.38  thf(dt_k6_partfun1, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( m1_subset_1 @
% 1.18/1.38         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.18/1.38       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.18/1.38  thf('87', plain,
% 1.18/1.38      (![X44 : $i]:
% 1.18/1.38         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 1.18/1.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 1.18/1.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.18/1.38  thf(redefinition_k6_partfun1, axiom,
% 1.18/1.38    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.18/1.38  thf('88', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.18/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.18/1.38  thf('89', plain,
% 1.18/1.38      (![X44 : $i]:
% 1.18/1.38         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 1.18/1.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 1.18/1.38      inference('demod', [status(thm)], ['87', '88'])).
% 1.18/1.38  thf('90', plain,
% 1.18/1.38      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['86', '89'])).
% 1.18/1.38  thf('91', plain,
% 1.18/1.38      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.18/1.38      inference('simplify', [status(thm)], ['85'])).
% 1.18/1.38  thf('92', plain,
% 1.18/1.38      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.38         (~ (v1_xboole_0 @ X20)
% 1.18/1.38          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 1.18/1.38          | (v1_xboole_0 @ X21))),
% 1.18/1.38      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.18/1.38  thf('93', plain,
% 1.18/1.38      (![X1 : $i]:
% 1.18/1.38         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.18/1.38          | (v1_xboole_0 @ X1)
% 1.18/1.38          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['91', '92'])).
% 1.18/1.38  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.38  thf('95', plain,
% 1.18/1.38      (![X1 : $i]:
% 1.18/1.38         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.18/1.38          | (v1_xboole_0 @ X1))),
% 1.18/1.38      inference('demod', [status(thm)], ['93', '94'])).
% 1.18/1.38  thf('96', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['90', '95'])).
% 1.18/1.38  thf('97', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.38  thf('98', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['96', '97'])).
% 1.18/1.38  thf(t72_relat_1, axiom,
% 1.18/1.38    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.18/1.38  thf('99', plain,
% 1.18/1.38      (![X11 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X11)) = (k6_relat_1 @ X11))),
% 1.18/1.38      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.18/1.38  thf('100', plain,
% 1.18/1.38      (((k4_relat_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['98', '99'])).
% 1.18/1.38  thf('101', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['96', '97'])).
% 1.18/1.38  thf('102', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['100', '101'])).
% 1.18/1.38  thf('103', plain,
% 1.18/1.38      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('demod', [status(thm)], ['73', '84', '102'])).
% 1.18/1.38  thf('104', plain,
% 1.18/1.38      ((((k1_xboole_0) = (sk_C)))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['80', '83'])).
% 1.18/1.38  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('106', plain,
% 1.18/1.38      (((v1_funct_1 @ k1_xboole_0))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup+', [status(thm)], ['104', '105'])).
% 1.18/1.38  thf('107', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['96', '97'])).
% 1.18/1.38  thf('108', plain, (![X43 : $i]: (v1_partfun1 @ (k6_partfun1 @ X43) @ X43)),
% 1.18/1.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.18/1.38  thf('109', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.18/1.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.18/1.38  thf('110', plain, (![X43 : $i]: (v1_partfun1 @ (k6_relat_1 @ X43) @ X43)),
% 1.18/1.38      inference('demod', [status(thm)], ['108', '109'])).
% 1.18/1.38  thf('111', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('sup+', [status(thm)], ['107', '110'])).
% 1.18/1.38  thf('112', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.38  thf(t4_subset_1, axiom,
% 1.18/1.38    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.18/1.38  thf('113', plain,
% 1.18/1.38      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 1.18/1.38      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.18/1.38  thf('114', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['112', '113'])).
% 1.18/1.38  thf(cc1_funct_2, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.38       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.18/1.38         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.18/1.38  thf('115', plain,
% 1.18/1.38      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.18/1.38         (~ (v1_funct_1 @ X29)
% 1.18/1.38          | ~ (v1_partfun1 @ X29 @ X30)
% 1.18/1.38          | (v1_funct_2 @ X29 @ X30 @ X31)
% 1.18/1.38          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.18/1.38      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.18/1.38  thf('116', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.38         (~ (v1_xboole_0 @ X2)
% 1.18/1.38          | (v1_funct_2 @ X2 @ X1 @ X0)
% 1.18/1.38          | ~ (v1_partfun1 @ X2 @ X1)
% 1.18/1.38          | ~ (v1_funct_1 @ X2))),
% 1.18/1.38      inference('sup-', [status(thm)], ['114', '115'])).
% 1.18/1.38  thf('117', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (v1_funct_1 @ k1_xboole_0)
% 1.18/1.38          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.18/1.38          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['111', '116'])).
% 1.18/1.38  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.38  thf('119', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (v1_funct_1 @ k1_xboole_0)
% 1.18/1.38          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.18/1.38      inference('demod', [status(thm)], ['117', '118'])).
% 1.18/1.38  thf('120', plain,
% 1.18/1.38      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 1.18/1.38         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['106', '119'])).
% 1.18/1.38  thf('121', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.18/1.38      inference('demod', [status(thm)], ['103', '120'])).
% 1.18/1.38  thf('122', plain,
% 1.18/1.38      (~
% 1.18/1.38       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.18/1.38       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.18/1.38       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.18/1.38      inference('split', [status(esa)], ['0'])).
% 1.18/1.38  thf('123', plain,
% 1.18/1.38      (~
% 1.18/1.38       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.18/1.38      inference('sat_resolution*', [status(thm)], ['17', '121', '122'])).
% 1.18/1.38  thf('124', plain,
% 1.18/1.38      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.38      inference('simpl_trail', [status(thm)], ['10', '123'])).
% 1.18/1.38  thf('125', plain,
% 1.18/1.38      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.18/1.38  thf('126', plain,
% 1.18/1.38      (![X35 : $i, X36 : $i]:
% 1.18/1.38         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.38  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.38  thf('128', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.18/1.38      inference('sup+', [status(thm)], ['126', '127'])).
% 1.18/1.38  thf('129', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.38  thf('130', plain,
% 1.18/1.38      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.18/1.38      inference('simplify', [status(thm)], ['85'])).
% 1.18/1.38  thf('131', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['129', '130'])).
% 1.18/1.38  thf('132', plain,
% 1.18/1.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('133', plain,
% 1.18/1.38      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.18/1.38        | ~ (v1_xboole_0 @ sk_B))),
% 1.18/1.38      inference('sup+', [status(thm)], ['131', '132'])).
% 1.18/1.38  thf('134', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         ((zip_tseitin_0 @ sk_B @ X0)
% 1.18/1.38          | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['128', '133'])).
% 1.18/1.38  thf('135', plain,
% 1.18/1.38      (![X1 : $i]:
% 1.18/1.38         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.18/1.38          | (v1_xboole_0 @ X1))),
% 1.18/1.38      inference('demod', [status(thm)], ['93', '94'])).
% 1.18/1.38  thf('136', plain,
% 1.18/1.38      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 1.18/1.38      inference('sup-', [status(thm)], ['134', '135'])).
% 1.18/1.38  thf('137', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.38  thf('138', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['100', '101'])).
% 1.18/1.38  thf('139', plain,
% 1.18/1.38      (![X0 : $i]: (((k1_xboole_0) = (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['137', '138'])).
% 1.18/1.38  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.38  thf('141', plain,
% 1.18/1.38      (![X0 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['139', '140'])).
% 1.18/1.38  thf('142', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.18/1.38  thf('143', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['112', '113'])).
% 1.18/1.38  thf('144', plain,
% 1.18/1.38      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('split', [status(esa)], ['0'])).
% 1.18/1.38  thf('145', plain,
% 1.18/1.38      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['143', '144'])).
% 1.18/1.38  thf('146', plain,
% 1.18/1.38      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['142', '145'])).
% 1.18/1.38  thf('147', plain,
% 1.18/1.38      ((~ (v1_xboole_0 @ sk_C))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['141', '146'])).
% 1.18/1.38  thf('148', plain,
% 1.18/1.38      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['136', '147'])).
% 1.18/1.38  thf('149', plain,
% 1.18/1.38      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.18/1.38      inference('sup-', [status(thm)], ['21', '22'])).
% 1.18/1.38  thf('150', plain,
% 1.18/1.38      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['148', '149'])).
% 1.18/1.38  thf('151', plain,
% 1.18/1.38      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['27', '30'])).
% 1.18/1.38  thf('152', plain,
% 1.18/1.38      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.18/1.38         <= (~
% 1.18/1.38             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['150', '151'])).
% 1.18/1.38  thf('153', plain,
% 1.18/1.38      (~
% 1.18/1.38       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.18/1.38      inference('sat_resolution*', [status(thm)], ['17', '121', '122'])).
% 1.18/1.38  thf('154', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.18/1.38      inference('simpl_trail', [status(thm)], ['152', '153'])).
% 1.18/1.38  thf('155', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['125', '154'])).
% 1.18/1.38  thf('156', plain,
% 1.18/1.38      (![X46 : $i]:
% 1.18/1.38         ((m1_subset_1 @ X46 @ 
% 1.18/1.38           (k1_zfmisc_1 @ 
% 1.18/1.38            (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46))))
% 1.18/1.38          | ~ (v1_funct_1 @ X46)
% 1.18/1.38          | ~ (v1_relat_1 @ X46))),
% 1.18/1.38      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.18/1.38  thf('157', plain,
% 1.18/1.38      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.38         (k1_zfmisc_1 @ 
% 1.18/1.38          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 1.18/1.38        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.18/1.38        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('sup+', [status(thm)], ['155', '156'])).
% 1.18/1.38  thf('158', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.38      inference('demod', [status(thm)], ['39', '44'])).
% 1.18/1.38  thf('159', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.18/1.38  thf('160', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.18/1.38      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.18/1.38  thf('161', plain,
% 1.18/1.38      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.38      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 1.18/1.38  thf('162', plain, ($false), inference('demod', [status(thm)], ['124', '161'])).
% 1.18/1.38  
% 1.18/1.38  % SZS output end Refutation
% 1.18/1.38  
% 1.18/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
