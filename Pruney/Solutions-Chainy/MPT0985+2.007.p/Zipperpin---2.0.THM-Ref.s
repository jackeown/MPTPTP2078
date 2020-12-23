%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K67NEYwp59

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:28 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  216 (1664 expanded)
%              Number of leaves         :   48 ( 526 expanded)
%              Depth                    :   24
%              Number of atoms          : 1424 (24221 expanded)
%              Number of equality atoms :   96 ( 904 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_funct_1 @ X27 )
        = ( k4_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

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
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

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
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X45 @ X43 )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X54: $i] :
      ( ( v1_funct_2 @ X54 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('47',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('49',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('56',plain,(
    ! [X28: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('62',plain,(
    ! [X28: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('65',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','54','60','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','67'])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('80',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('82',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('86',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','103'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('105',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('107',plain,(
    ! [X14: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X55 ) @ X56 )
      | ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ X56 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('115',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('118',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf('120',plain,(
    ! [X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('123',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','118','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['73','99','104','128'])).

thf('130',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','129','130'])).

thf('132',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('134',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('138',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('141',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C_1 ) @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('147',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B_1 @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('154',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('156',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','129','130'])).

thf('158',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['156','157'])).

thf('159',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['133','158'])).

thf('160',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X54 ) ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('161',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('163',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('164',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('165',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['132','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K67NEYwp59
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 896 iterations in 0.642s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.10  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.10  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.90/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.10  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.10  thf(t31_funct_2, conjecture,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.10       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.90/1.10         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.90/1.10           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.90/1.10           ( m1_subset_1 @
% 0.90/1.10             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.10          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.90/1.10            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.90/1.10              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.90/1.10              ( m1_subset_1 @
% 0.90/1.10                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.90/1.10  thf('0', plain,
% 0.90/1.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.90/1.10        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 0.90/1.10        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.90/1.10         <= (~
% 0.90/1.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(cc1_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( v1_relat_1 @ C ) ))).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.10         ((v1_relat_1 @ X34)
% 0.90/1.10          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.90/1.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.10  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf(d9_funct_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.10       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      (![X27 : $i]:
% 0.90/1.10         (~ (v2_funct_1 @ X27)
% 0.90/1.10          | ((k2_funct_1 @ X27) = (k4_relat_1 @ X27))
% 0.90/1.10          | ~ (v1_funct_1 @ X27)
% 0.90/1.10          | ~ (v1_relat_1 @ X27))),
% 0.90/1.10      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      ((~ (v1_funct_1 @ sk_C_1)
% 0.90/1.10        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 0.90/1.10        | ~ (v2_funct_1 @ sk_C_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.10  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('8', plain, ((v2_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('9', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.90/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.90/1.10         <= (~
% 0.90/1.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.10      inference('demod', [status(thm)], ['1', '9'])).
% 0.90/1.10  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf(dt_k2_funct_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.10       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.10         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (![X28 : $i]:
% 0.90/1.10         ((v1_funct_1 @ (k2_funct_1 @ X28))
% 0.90/1.10          | ~ (v1_funct_1 @ X28)
% 0.90/1.10          | ~ (v1_relat_1 @ X28))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.90/1.10         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.90/1.10         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.10  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.90/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.10  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['11', '16'])).
% 0.90/1.10  thf('18', plain,
% 0.90/1.10      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.90/1.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('19', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.10  thf(d1_funct_2, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.10           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.10             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.10           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.10             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_1, axiom,
% 0.90/1.10    (![B:$i,A:$i]:
% 0.90/1.10     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.10       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.10  thf('20', plain,
% 0.90/1.10      (![X46 : $i, X47 : $i]:
% 0.90/1.10         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.10  thf(zf_stmt_3, axiom,
% 0.90/1.10    (![C:$i,B:$i,A:$i]:
% 0.90/1.10     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.10       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.10  thf(zf_stmt_5, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.10         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.10           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.10             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.10  thf('22', plain,
% 0.90/1.10      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.90/1.10         (~ (zip_tseitin_0 @ X51 @ X52)
% 0.90/1.10          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 0.90/1.10          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.90/1.10        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['20', '23'])).
% 0.90/1.10  thf('25', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.90/1.10         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 0.90/1.10          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 0.90/1.10          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.90/1.10        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.10  thf('29', plain,
% 0.90/1.10      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.90/1.10         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.90/1.10          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.90/1.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.10  thf('30', plain,
% 0.90/1.10      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.90/1.10        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['27', '30'])).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['24', '31'])).
% 0.90/1.10  thf('33', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.10  thf(t55_funct_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.10       ( ( v2_funct_1 @ A ) =>
% 0.90/1.10         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.90/1.10           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.10  thf('34', plain,
% 0.90/1.10      (![X33 : $i]:
% 0.90/1.10         (~ (v2_funct_1 @ X33)
% 0.90/1.10          | ((k2_relat_1 @ X33) = (k1_relat_1 @ (k2_funct_1 @ X33)))
% 0.90/1.10          | ~ (v1_funct_1 @ X33)
% 0.90/1.10          | ~ (v1_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_C_1)
% 0.90/1.10        | ~ (v1_funct_1 @ sk_C_1)
% 0.90/1.10        | ~ (v2_funct_1 @ sk_C_1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['33', '34'])).
% 0.90/1.10  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('38', plain, ((v2_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('39', plain,
% 0.90/1.10      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.10  thf('41', plain,
% 0.90/1.10      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.90/1.10         (((k2_relset_1 @ X44 @ X45 @ X43) = (k2_relat_1 @ X43))
% 0.90/1.10          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.90/1.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.10  thf('42', plain,
% 0.90/1.10      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.10  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('44', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['42', '43'])).
% 0.90/1.10  thf('45', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['39', '44'])).
% 0.90/1.10  thf(t3_funct_2, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.10       ( ( v1_funct_1 @ A ) & 
% 0.90/1.10         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.90/1.10         ( m1_subset_1 @
% 0.90/1.10           A @ 
% 0.90/1.10           ( k1_zfmisc_1 @
% 0.90/1.10             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.10  thf('46', plain,
% 0.90/1.10      (![X54 : $i]:
% 0.90/1.10         ((v1_funct_2 @ X54 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))
% 0.90/1.10          | ~ (v1_funct_1 @ X54)
% 0.90/1.10          | ~ (v1_relat_1 @ X54))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ 
% 0.90/1.10         (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.90/1.10        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.90/1.10        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.90/1.10  thf('48', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      (![X33 : $i]:
% 0.90/1.10         (~ (v2_funct_1 @ X33)
% 0.90/1.10          | ((k1_relat_1 @ X33) = (k2_relat_1 @ (k2_funct_1 @ X33)))
% 0.90/1.10          | ~ (v1_funct_1 @ X33)
% 0.90/1.10          | ~ (v1_relat_1 @ X33))),
% 0.90/1.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_C_1)
% 0.90/1.10        | ~ (v1_funct_1 @ sk_C_1)
% 0.90/1.10        | ~ (v2_funct_1 @ sk_C_1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['48', '49'])).
% 0.90/1.10  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('53', plain, ((v2_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.10  thf('55', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.10  thf('56', plain,
% 0.90/1.10      (![X28 : $i]:
% 0.90/1.10         ((v1_relat_1 @ (k2_funct_1 @ X28))
% 0.90/1.10          | ~ (v1_funct_1 @ X28)
% 0.90/1.10          | ~ (v1_relat_1 @ X28))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.90/1.10        | ~ (v1_relat_1 @ sk_C_1)
% 0.90/1.10        | ~ (v1_funct_1 @ sk_C_1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['55', '56'])).
% 0.90/1.10  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('60', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.10  thf('61', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      (![X28 : $i]:
% 0.90/1.10         ((v1_funct_1 @ (k2_funct_1 @ X28))
% 0.90/1.11          | ~ (v1_funct_1 @ X28)
% 0.90/1.11          | ~ (v1_relat_1 @ X28))),
% 0.90/1.11      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.11  thf('63', plain,
% 0.90/1.11      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 0.90/1.11        | ~ (v1_relat_1 @ sk_C_1)
% 0.90/1.11        | ~ (v1_funct_1 @ sk_C_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['61', '62'])).
% 0.90/1.11  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('67', plain,
% 0.90/1.11      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['47', '54', '60', '66'])).
% 0.90/1.11  thf('68', plain,
% 0.90/1.11      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 0.90/1.11        | ((sk_B_1) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['32', '67'])).
% 0.90/1.11  thf('69', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.11  thf('70', plain,
% 0.90/1.11      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('split', [status(esa)], ['0'])).
% 0.90/1.11  thf('71', plain,
% 0.90/1.11      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.11  thf('72', plain,
% 0.90/1.11      ((((sk_B_1) = (k1_xboole_0)))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['68', '71'])).
% 0.90/1.11  thf('73', plain,
% 0.90/1.11      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('demod', [status(thm)], ['18', '19', '72'])).
% 0.90/1.11  thf('74', plain,
% 0.90/1.11      ((((sk_B_1) = (k1_xboole_0)))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['68', '71'])).
% 0.90/1.11  thf('75', plain,
% 0.90/1.11      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.90/1.11  thf(t65_relat_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( v1_relat_1 @ A ) =>
% 0.90/1.11       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.90/1.11         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.11  thf('76', plain,
% 0.90/1.11      (![X22 : $i]:
% 0.90/1.11         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.90/1.11          | ((k2_relat_1 @ X22) = (k1_xboole_0))
% 0.90/1.11          | ~ (v1_relat_1 @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.90/1.11  thf('77', plain,
% 0.90/1.11      ((((k2_relat_1 @ sk_C_1) != (k1_xboole_0))
% 0.90/1.11        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.90/1.11        | ((k2_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['75', '76'])).
% 0.90/1.11  thf('78', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.11  thf('79', plain,
% 0.90/1.11      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.11  thf('80', plain,
% 0.90/1.11      ((((k2_relat_1 @ sk_C_1) != (k1_xboole_0))
% 0.90/1.11        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.90/1.11  thf('81', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['42', '43'])).
% 0.90/1.11  thf('82', plain,
% 0.90/1.11      ((((sk_B_1) != (k1_xboole_0)) | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['80', '81'])).
% 0.90/1.11  thf('83', plain,
% 0.90/1.11      (((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.11         | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['74', '82'])).
% 0.90/1.11  thf('84', plain,
% 0.90/1.11      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('simplify', [status(thm)], ['83'])).
% 0.90/1.11  thf(fc8_relat_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.90/1.11       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.90/1.11  thf('85', plain,
% 0.90/1.11      (![X16 : $i]:
% 0.90/1.11         (~ (v1_xboole_0 @ (k1_relat_1 @ X16))
% 0.90/1.11          | ~ (v1_relat_1 @ X16)
% 0.90/1.11          | (v1_xboole_0 @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.90/1.11  thf('86', plain,
% 0.90/1.11      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.11         | (v1_xboole_0 @ sk_C_1)
% 0.90/1.11         | ~ (v1_relat_1 @ sk_C_1)))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['84', '85'])).
% 0.90/1.11  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.11  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.11  thf('88', plain, ((v1_relat_1 @ sk_C_1)),
% 0.90/1.11      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf('89', plain,
% 0.90/1.11      (((v1_xboole_0 @ sk_C_1))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.90/1.11  thf(d3_tarski, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.11       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.11  thf('90', plain,
% 0.90/1.11      (![X4 : $i, X6 : $i]:
% 0.90/1.11         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.90/1.11      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.11  thf(d1_xboole_0, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.11  thf('91', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.11  thf('92', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.11  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.11  thf('94', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.11  thf('95', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.11  thf(d10_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.11  thf('96', plain,
% 0.90/1.11      (![X7 : $i, X9 : $i]:
% 0.90/1.11         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('97', plain,
% 0.90/1.11      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['95', '96'])).
% 0.90/1.11  thf('98', plain,
% 0.90/1.11      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['92', '97'])).
% 0.90/1.11  thf('99', plain,
% 0.90/1.11      ((((sk_C_1) = (k1_xboole_0)))
% 0.90/1.11         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['89', '98'])).
% 0.90/1.11  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.11  thf(fc14_relat_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( v1_xboole_0 @ A ) =>
% 0.90/1.11       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 0.90/1.11         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.90/1.11  thf('101', plain,
% 0.90/1.11      (![X15 : $i]:
% 0.90/1.11         ((v1_xboole_0 @ (k4_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 0.90/1.11      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.90/1.11  thf('102', plain,
% 0.90/1.11      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['92', '97'])).
% 0.90/1.11  thf('103', plain,
% 0.90/1.11      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.11  thf('104', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['100', '103'])).
% 0.90/1.11  thf(cc1_funct_1, axiom,
% 0.90/1.11    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.90/1.11  thf('105', plain,
% 0.90/1.11      (![X25 : $i]: ((v1_funct_1 @ X25) | ~ (v1_xboole_0 @ X25))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.90/1.11  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.11  thf(fc11_relat_1, axiom,
% 0.90/1.11    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.90/1.11  thf('107', plain,
% 0.90/1.11      (![X14 : $i]:
% 0.90/1.11         ((v1_xboole_0 @ (k2_relat_1 @ X14)) | ~ (v1_xboole_0 @ X14))),
% 0.90/1.11      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.90/1.11  thf('108', plain,
% 0.90/1.11      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['92', '97'])).
% 0.90/1.11  thf('109', plain,
% 0.90/1.11      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['107', '108'])).
% 0.90/1.11  thf('110', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['106', '109'])).
% 0.90/1.11  thf(t4_funct_2, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.11       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.90/1.11         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.90/1.11           ( m1_subset_1 @
% 0.90/1.11             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.90/1.11  thf('111', plain,
% 0.90/1.11      (![X55 : $i, X56 : $i]:
% 0.90/1.11         (~ (r1_tarski @ (k2_relat_1 @ X55) @ X56)
% 0.90/1.11          | (v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ X56)
% 0.90/1.11          | ~ (v1_funct_1 @ X55)
% 0.90/1.11          | ~ (v1_relat_1 @ X55))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.90/1.11  thf('112', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.90/1.11          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.11          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.90/1.11          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['110', '111'])).
% 0.90/1.11  thf('113', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.11  thf('114', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.11  thf(t3_subset, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.11  thf('115', plain,
% 0.90/1.11      (![X10 : $i, X12 : $i]:
% 0.90/1.11         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.90/1.11      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.11  thf('116', plain,
% 0.90/1.11      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['114', '115'])).
% 0.90/1.11  thf('117', plain,
% 0.90/1.11      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.11         ((v1_relat_1 @ X34)
% 0.90/1.11          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.90/1.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.11  thf('118', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['116', '117'])).
% 0.90/1.11  thf('119', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['106', '109'])).
% 0.90/1.11  thf('120', plain,
% 0.90/1.11      (![X22 : $i]:
% 0.90/1.11         (((k2_relat_1 @ X22) != (k1_xboole_0))
% 0.90/1.11          | ((k1_relat_1 @ X22) = (k1_xboole_0))
% 0.90/1.11          | ~ (v1_relat_1 @ X22))),
% 0.90/1.11      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.90/1.11  thf('121', plain,
% 0.90/1.11      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.11        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.11        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['119', '120'])).
% 0.90/1.11  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['116', '117'])).
% 0.90/1.11  thf('123', plain,
% 0.90/1.11      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.11        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['121', '122'])).
% 0.90/1.11  thf('124', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('simplify', [status(thm)], ['123'])).
% 0.90/1.11  thf('125', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v1_funct_1 @ k1_xboole_0)
% 0.90/1.11          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['112', '113', '118', '124'])).
% 0.90/1.11  thf('126', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.11          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['105', '125'])).
% 0.90/1.11  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.11  thf('128', plain,
% 0.90/1.11      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.90/1.11      inference('demod', [status(thm)], ['126', '127'])).
% 0.90/1.11  thf('129', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 0.90/1.11      inference('demod', [status(thm)], ['73', '99', '104', '128'])).
% 0.90/1.11  thf('130', plain,
% 0.90/1.11      (~
% 0.90/1.11       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 0.90/1.11       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)) | 
% 0.90/1.11       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.90/1.11      inference('split', [status(esa)], ['0'])).
% 0.90/1.11  thf('131', plain,
% 0.90/1.11      (~
% 0.90/1.11       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.11      inference('sat_resolution*', [status(thm)], ['17', '129', '130'])).
% 0.90/1.11  thf('132', plain,
% 0.90/1.11      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.90/1.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['10', '131'])).
% 0.90/1.11  thf('133', plain,
% 0.90/1.11      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.11  thf('134', plain,
% 0.90/1.11      (![X46 : $i, X47 : $i]:
% 0.90/1.11         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.11  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.11  thf('136', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['134', '135'])).
% 0.90/1.11  thf('137', plain,
% 0.90/1.11      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.90/1.11  thf('138', plain,
% 0.90/1.11      (![X16 : $i]:
% 0.90/1.11         (~ (v1_xboole_0 @ (k1_relat_1 @ X16))
% 0.90/1.11          | ~ (v1_relat_1 @ X16)
% 0.90/1.11          | (v1_xboole_0 @ X16))),
% 0.90/1.11      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.90/1.11  thf('139', plain,
% 0.90/1.11      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.90/1.11        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))
% 0.90/1.11        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['137', '138'])).
% 0.90/1.11  thf('140', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.11  thf('141', plain,
% 0.90/1.11      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.90/1.11        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['139', '140'])).
% 0.90/1.11  thf('142', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((zip_tseitin_0 @ (k2_relat_1 @ sk_C_1) @ X0)
% 0.90/1.11          | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['136', '141'])).
% 0.90/1.11  thf('143', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['42', '43'])).
% 0.90/1.11  thf('144', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['142', '143'])).
% 0.90/1.11  thf('145', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.90/1.11  thf('146', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.11  thf('147', plain,
% 0.90/1.11      (![X10 : $i, X12 : $i]:
% 0.90/1.11         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.90/1.11      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.11  thf('148', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['146', '147'])).
% 0.90/1.11  thf('149', plain,
% 0.90/1.11      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.90/1.11         <= (~
% 0.90/1.11             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.11      inference('split', [status(esa)], ['0'])).
% 0.90/1.11  thf('150', plain,
% 0.90/1.11      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1)))
% 0.90/1.11         <= (~
% 0.90/1.11             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['148', '149'])).
% 0.90/1.11  thf('151', plain,
% 0.90/1.11      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))
% 0.90/1.11         <= (~
% 0.90/1.11             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['145', '150'])).
% 0.90/1.11  thf('152', plain,
% 0.90/1.11      ((![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0))
% 0.90/1.11         <= (~
% 0.90/1.11             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['144', '151'])).
% 0.90/1.11  thf('153', plain,
% 0.90/1.11      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.90/1.11        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.90/1.11      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.11  thf('154', plain,
% 0.90/1.11      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))
% 0.90/1.11         <= (~
% 0.90/1.11             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['152', '153'])).
% 0.90/1.11  thf('155', plain,
% 0.90/1.11      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.90/1.11        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['27', '30'])).
% 0.90/1.11  thf('156', plain,
% 0.90/1.11      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 0.90/1.11         <= (~
% 0.90/1.11             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['154', '155'])).
% 0.90/1.11  thf('157', plain,
% 0.90/1.11      (~
% 0.90/1.11       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.90/1.11         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.90/1.11      inference('sat_resolution*', [status(thm)], ['17', '129', '130'])).
% 0.90/1.11  thf('158', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['156', '157'])).
% 0.90/1.11  thf('159', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['133', '158'])).
% 0.90/1.11  thf('160', plain,
% 0.90/1.11      (![X54 : $i]:
% 0.90/1.11         ((m1_subset_1 @ X54 @ 
% 0.90/1.11           (k1_zfmisc_1 @ 
% 0.90/1.11            (k2_zfmisc_1 @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X54))))
% 0.90/1.11          | ~ (v1_funct_1 @ X54)
% 0.90/1.11          | ~ (v1_relat_1 @ X54))),
% 0.90/1.11      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.90/1.11  thf('161', plain,
% 0.90/1.11      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.90/1.11         (k1_zfmisc_1 @ 
% 0.90/1.11          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)))
% 0.90/1.11        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.90/1.11        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['159', '160'])).
% 0.90/1.11  thf('162', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['39', '44'])).
% 0.90/1.11  thf('163', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.11  thf('164', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.11  thf('165', plain,
% 0.90/1.11      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.90/1.11        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.11      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 0.90/1.11  thf('166', plain, ($false), inference('demod', [status(thm)], ['132', '165'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
